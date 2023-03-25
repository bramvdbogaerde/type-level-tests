package typeprogramming

trait HMapKey:
  type Value
object HMapKey:
  type Aux[V] = HMapKey { type Value = V }

case class HMap(contents: Map[Any, Any]):
  def get(k: HMapKey): Option[k.Value] =
    // SAFETY: asInstanceOf is safe as only values corresponding to their key type can be added to the HMap (using put)
    contents.get(k).map(_.asInstanceOf[k.Value])
  def put(k: HMapKey, v: k.Value): HMap =
    this.copy(contents = contents + (k -> v))

object HMap:
  def empty: HMap = HMap(Map())
