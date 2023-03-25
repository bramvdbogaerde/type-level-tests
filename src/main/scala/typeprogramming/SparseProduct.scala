package typeprogramming

import scala.annotation.implicitNotFound

/** A typelevel constructor for a product value, takes a left and a right value
  * that should be part of the product
  */
trait :*:[L, R]

/** A tuple for tagging the elements in the product value */
trait ~>[K, V]

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
// HMap interpretation
//

case class HMapProductKey[K, V](k: K) extends HMapKey:
  type Value = V

class HMapProduct[P: Product] private (map: HMap) {
  def get[K, V](key: K)(using
      KeyValueIn[K, V, P]
  ): Option[V] = map.get(HMapProductKey(key))

  def put[K, V](key: K, vlu: V)(using KeyValueIn[K, V, P]): HMapProduct[P] =
    HMapProduct(map.put(HMapProductKey(key), vlu))
}

object HMapProduct:
  def empty[P: Product]: HMapProduct[P] = HMapProduct(HMap.empty)

// Examples
object Examples extends App {
  trait Tag
  object IntT extends Tag
  type IntT = IntT.type
  object PrimT extends Tag
  type PrimT = PrimT.type
  object StrT extends Tag
  type StrT = StrT.type
  object RealT extends Tag
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

}
