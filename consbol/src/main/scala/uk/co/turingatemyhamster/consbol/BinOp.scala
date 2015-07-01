package uk.co.turingatemyhamster.consbol

/**
 * Created by nmrp3 on 01/07/15.
 */
object BinOp {

  def apply[O[_], T](r: (T, T) => O[T], d: O[T] => Option[(T, T)]): BinOp[O[T], T] = new BinOp[O[T], T] {
    override def recompose(tt: (T, T)): O[T] = r.tupled(tt)

    override def decompose(o: O[T]): (T, T) = d(o).get
  }

  implicit def ltBinOp[T]: BinOp[LT[T], T] = BinOp(LT.apply, LT.unapply)
  implicit def ltEqBinOp[T]: BinOp[LT_EQ[T], T] = BinOp(LT_EQ.apply, LT_EQ.unapply)
  implicit def eqBinOp[T]: BinOp[EQ[T], T] = BinOp(EQ.apply, EQ.unapply)
  implicit def notEqBinOp[T]: BinOp[NOT_EQ[T], T] = BinOp(NOT_EQ.apply, NOT_EQ.unapply)
}

trait BinOp[O, T] {
  def decompose(o: O): (T, T)
  def recompose(tt: (T, T)): O
}