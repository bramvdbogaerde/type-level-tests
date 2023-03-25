package typeprogramming

import scala.annotation.implicitNotFound

/** A typelevel constructor for a product value, takes a left and a right value
  * that should be part of the product
  */
trait :*:[L, R]

/** A tuple for tagging the elements in the product value */
trait ~>[K, V]

//
// Keys
//

/** Return a key in the value domain for type K */
trait KeyFor[K]:
  def key: K

/** A key that is implicitly available for some K */
trait Key[K]:
  outer: K =>

  given KeyFor[K] with
    def key: K = outer

//
// Membership
//

/** Predicate that is satisfied if the product value contains a pair with the
  * given key and value type
  */
@implicitNotFound("Key ${K} is not in product ${P}")
trait KeyValueIn[K, V, P]

/** Base case */
given [K, V]: KeyValueIn[K, V, (K ~> V)] with {}

/** If the key is in front of the product than it is in the product */
given [K, V, P]: KeyValueIn[K, V, (K ~> V) :*: P] with {}

/** If the key is not in front of the product, then it must be in its remainder
  */
given keyInRemainder[K1, K2, V, R](using
    KeyValueIn[K1, V, R]
): KeyValueIn[K1, V, K2 :*: R] with {}

//
// Duplication tests
//

/** Predicate that is satisfied if the product does not contain any duplicate
  * keys
  */
trait NoDuplicates[P]

/** Auxilary predicate to iteratively check that the product does not contain
  * any duplicate keys
  */
trait NoDuplicatesAux[P, L <: HList]

/** Entry */
given [P](using NoDuplicatesAux[P, HNil]): NoDuplicates[P] with {}

/** End of the product */
given [K, V, L <: HList](using ContainsNot[K, L]): NoDuplicatesAux[(K ~> V), L]
  with {}

/** The first one should not be already in the list of seen elements */
given [K, V, R, L <: HList](using
    NoDuplicatesAux[R, K :: L],
    ContainsNot[K, L]
): NoDuplicatesAux[(K ~> V) :*: R, L] with {}

/** A well-formed product type should not contain any duplicates */
trait Product[P]
given [P](using NoDuplicates[P]): Product[P] with {}

//
// (Sparse) HMap interpretation
//

case class HMapProductKey[K, V](k: K) extends HMapKey:
  type Value = V

class HMapProduct[P: Product] private (map: HMap) {

  type Self[P] = HMapProduct[P]

  def get[K, V](key: K)(using
      KeyValueIn[K, V, P]
  ): Option[V] = map.get(HMapProductKey(key))

  def put[K, V](key: K, vlu: V)(using KeyValueIn[K, V, P]): Self[P] =
    HMapProduct(map.put(HMapProductKey(key), vlu))

}

object HMapProduct:
  def empty[P: Product]: HMapProduct[P] = HMapProduct(HMap.empty)

//
// A tagged tuple implementation
//

/** A (non-sparse) version of a product, ensures that all keys in the product
  * are available
  */
class TaggedTuple[P: Product] private (map: HMap) {
  def get[K, V](key: K)(using
      KeyValueIn[K, V, P]
  ): V = map.get(HMapProductKey(key)).get

  def extend[K, V](using
      NoDuplicates[(K ~> V) :*: P]
  )(key: K, vlu: V): TaggedTuple[(K ~> V) :*: P] =
    TaggedTuple(map.put(HMapProductKey(key), vlu))
}

object TaggedTuple:
  def initial[K, V](k: K, v: V): TaggedTuple[(K ~> V)] =
    TaggedTuple(HMap.empty.put(HMapProductKey(k), v))

//
// Utilities
//

/* Summon instances of a particular type for all the values in the product */
trait SummonForValues[IP, P]:
  def instances: TaggedTuple[IP]

given [F[_], K, V](using
    instance: F[V],
    key: KeyFor[K]
): SummonForValues[(K ~> F[V]), (K ~> V)] with {

  def instances: TaggedTuple[K ~> F[V]] =
    TaggedTuple.initial[K, F[V]](key.key, instance)
}

given [F[_], K, V, P, IP](using
    instance: F[V],
    summonForAll: SummonForValues[IP, P],
    noDup: NoDuplicates[(K ~> F[V]) :*: IP],
    key: KeyFor[K]
): SummonForValues[(K ~> F[V]) :*: IP, (K ~> V) :*: P] with {
  def instances: TaggedTuple[(K ~> F[V]) :*: IP] =
    summonForAll.instances
      .extend[K, F[V]](key.key, instance)
}

// Examples
object Examples extends App {
  object IntT extends Key[IntT]
  type IntT = IntT.type
  object PrimT extends Key[PrimT]
  type PrimT = PrimT.type
  object StrT extends Key[StrT]
  type StrT = StrT.type
  object RealT extends Key[RealT]
  type RealT = RealT.type

  trait CP[+X]
  case object Bottom extends CP[Nothing]
  case class Constant[X](c: X) extends CP[X]
  case object Top extends CP[Nothing]

  type ModularProductValue[I, S] =
    (IntT ~> I) :*: (StrT ~> S) :*: (PrimT ~> Set[String])

  // the product below is bad since it contains keys StrT twice
  type BadProductValue =
    (IntT ~> CP[Int]) :*: (StrT ~> CP[String]) :*: (StrT ~> Set[String])

  // succeeds
  summon[Product[ModularProductValue[CP[Int], CP[String]]]]

  // fails
  // summon[Product[BadProductValue]]

  // Key to value level
  summon[KeyFor[IntT]]

  // Insertion

  // succeeds
  val exampleMap1: HMapProduct[ModularProductValue[CP[Int], CP[String]]] =
    HMapProduct.empty
      .put(IntT, Constant(4): CP[Int])
      .put(PrimT, Set("+", "-"): Set[String])

  // fails since the the given key is not in the product
  // val exampleMap2: HMapProduct[ProductValue] =
  //   HMapProduct.empty
  //     .put(RealT, Constant(42.3))

  // Lookup
  // succeeds
  assert((exampleMap1.get(IntT): Option[CP[Int]]) == Some(Constant(4)))

  // fails at compile time since key is not in the product
  // assert((exampleMap1.get(RealT): Option[CP[Double]]) == None)

  // summon values for the product

  trait Lattice[L]:
    def join(a: L, b: => L): L

  given [X]: Lattice[CP[X]] with
    def join(a: CP[X], b: => CP[X]): CP[X] = (a, b) match
      case (Top, _) | (_, Top)        => Top
      case (Constant(x), Constant(y)) => Top
      case (Bottom, x)                => x
      case (y, Bottom)                => y

  given [X]: Lattice[Set[X]] with
    def join(a: Set[X], b: => Set[X]): Set[X] = a.union(b)

  type Lattices = (IntT ~> Lattice[CP[Int]]) :*:
    (StrT ~> Lattice[CP[String]]) :*: (PrimT ~> Lattice[Set[String]])

  val lattices =
    summon[SummonForValues[Lattices, ModularProductValue[CP[
      Int
    ], CP[
      String
    ]]]].instances

  assert(lattices.get(IntT).join(Constant(4), Constant(5)) == Top)
  assert(lattices.get(PrimT).join(Set("+"), Set("-")) == Set("+", "-"))
}
