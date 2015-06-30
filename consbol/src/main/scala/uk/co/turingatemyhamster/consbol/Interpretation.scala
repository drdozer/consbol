package uk.co.turingatemyhamster.consbol


trait Interpretation[TV, TI, M] {
  def apply(a: TV, m: M): (TI, M)
}

object Interpretation {

  implicit class InterpretationOps[M](val _m: M) {
    def interpretation[TV, TI](a: TV)(implicit in: Interpretation[TV, TI, M]): (TI, M) =
      in.apply(a, _m)
  }

  implicit def interpModel[V, I]
  (implicit vi: InterpretationSingleton[V, I])
  : Interpretation[V, I, InterpModel[V, I]] = new Interpretation[V, I, InterpModel[V, I]] {
    override def apply(a: V, m0: InterpModel[V, I]): (I, InterpModel[V, I]) =
      m0.v2i.get(a) match {
        case Some(aI) =>
          (aI, m0)
        case None =>
          val aI = vi.singleton(a)
          val m1 = m0.copy(
            v2i = m0.v2i + (a -> aI),
            eq = m0.eq + (aI -> Set(a)))
          (aI, m1)
      }
  }

  implicit def model[V, I](implicit imI: Interpretation[V, I, InterpModel[V, I]])
  : Interpretation[V, I, Model[V, I]] = new Interpretation[V, I, Model[V, I]] {
    override def apply(a: V, m: Model[V, I]): (I, Model[V, I]) = {
      val (aI, i2) = m.i interpretation a
      (aI, m.copy(i = i2))
    }
  }

  implicit def opInterpolation[A[_], V, I]
  (implicit vOp: BinOp[A[V], V], iOp: BinOp[A[I], I], viI: Interpretation[V, I, Model[V, I]])
  : Interpretation[A[V], A[I], Model[V, I]] = new Interpretation[A[V], A[I], Model[V, I]]
  {
    override def apply(a: A[V], m0: Model[V, I]): (A[I], Model[V, I]) = {
      val (lhsV, rhsV) = vOp.decompose(a)
      val (lhsI, m1) = m0 interpretation lhsV
      val (rhsI, m2) = m1 interpretation rhsV
      iOp.recompose(lhsI, rhsI) -> m2
    }
  }
}


trait Interpretations[I, M] {
  def apply(m: M): Iterable[I]
}

object Interpretations {

  implicit class InterpretationsOps[M](val _m: M) {
    def allInterpretations[I](implicit in: Interpretations[I, M]): Iterable[I] =
      in.apply(_m)
  }

  implicit def interpretations_interpModel[V, I]
  : Interpretations[I, InterpModel[V, I]] = new Interpretations[I, InterpModel[V, I]] {
    override def apply(m: InterpModel[V, I]): Iterable[I] =
      m.eq.keys
  }

  implicit def interpretations_model[V, I]
  : Interpretations[I, Model[V, I]] = new Interpretations[I, Model[V, I]] {
    override def apply(m: Model[V, I]): Iterable[I] =
      m.i.allInterpretations
  }

}


trait InterpretationSingleton[V, I] {
  def singleton(v: V): I

  def coMap[VV](f: VV => V): InterpretationSingleton[VV, I] = {
    val outer = this
    new InterpretationSingleton[VV, I] {
      override def singleton(v: VV): I = outer.singleton(f(v))
    }
  }
}

object InterpretationSingleton {
  implicit val strVI: InterpretationSingleton[String, String] = new InterpretationSingleton[String, String] {
    override def singleton(v: String): String = v
  }

  implicit val symVI: InterpretationSingleton[Symbol, String] = strVI.coMap(_.toString)
}


trait UnifyI[I] {
  def apply(a: I, b: I): I
}

object UnifyI {
  implicit val strUnifyI: UnifyI[String] = new UnifyI[String] {
    override def apply(a: String, b: String): String = a + ":" + b
  }
}
