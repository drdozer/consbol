package uk.co.turingatemyhamster.consbol


trait Unifier[I, M] {
  def apply(aI: I, bI: I, uI: I, m: M): M
}

object Unifier {

  implicit class UnifierOps[M](m: M) {
    def unify[I](aI: I, bI: I, uI: I)(implicit u: Unifier[I, M]): M =
      u(aI, bI, uI, m)
  }

  def subst[I](a: I, b: I, x: I)(ij: (I, I)): (I, I) = ij match {
    case (i, j) =>
      (if(i == a || i == b) x else i,
        if(j == a || j == b) x else j)
  }

  implicit def modelUnifier[R, V, I]
  (implicit
   iU: Unifier[I, InterpModel[V, I]],
   ordU: Unifier[I, OrdModel[I]],
   indexU: Unifier[I, IndexModel[I]])
  : Unifier[I, Model[R, V, I]] = new Unifier[I, Model[R, V, I]] {
    override def apply(aI: I, bI: I, uI: I, m: Model[R, V, I]): Model[R, V, I] =
      Model(
        i = iU(aI, bI, uI, m.i),
        ord = ordU(aI, bI, uI, m.ord),
        index = indexU(aI, bI, uI, m.index),
        range = m.range,
        str = m.str,
        length = m.length)
  }

  implicit def interpretationUnifier[V, I]: Unifier[I, InterpModel[V, I]] = new Unifier[I, InterpModel[V, I]] {
    override def apply(aI: I, bI: I, uI: I, interp: InterpModel[V, I]): InterpModel[V, I] = {
      val eqA = interp.eq(aI)
      val eqB = interp.eq(bI)
      val eqU = eqA ++ eqB

      interp.copy(eq = interp.eq - aI - bI + (uI -> eqU))
    }
  }

  implicit def ordModelUnifier[I]: Unifier[I, OrdModel[I]] = new Unifier[I, OrdModel[I]] {
    override def apply(aI: I, bI: I, uI: I, m: OrdModel[I]): OrdModel[I] = {
      val sub = subst(aI, bI, uI) _
      OrdModel(
        lt = m.lt map sub,
        lt_eq = m.lt_eq map sub,
        not_eq = m.not_eq map sub)
    }
  }

  implicit def indexModelUnifier[I]: Unifier[I, IndexModel[I]] = new Unifier[I, IndexModel[I]] {
    override def apply(aI: I, bI: I, uI: I, m: IndexModel[I]): IndexModel[I] = {
      val saI = m.at.getOrElse(aI, Set())
      val sbI = m.at.getOrElse(bI, Set())
      val suI = saI ++ sbI

      IndexModel(
        at = m.at - aI - bI + (uI -> suI))
    }
  }

  implicit def rangeModelUnifier[R, I]: Unifier[I, RangeModel[R, I]] = new Unifier[I, RangeModel[R, I]] {
    override def apply(aI: I, bI: I, uI: I, m: RangeModel[R, I]): RangeModel[R, I] = {
      RangeModel(
        rangeAs = m.rangeAs
      )
    }
  }
}
