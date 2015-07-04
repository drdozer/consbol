package uk.co.turingatemyhamster.consbol

import scalaz.{Need, StreamT}


trait Interpretation[TV, TI, M] {
  def apply(a: TV, m: M): (TI, M)
  def unapply(a: TI, m: M): Option[TV]
}

object Interpretation {

  implicit class InterpretationOps[M](val _m: M) {
    def interpretation[TV, TI](a: TV)(implicit in: Interpretation[TV, TI, M]): (TI, M) =
      in.apply(a, _m)

    def coimage[TV, TI](a: TI)(implicit in: Interpretation[TV, TI, M]): Option[TV] =
      in.unapply(a, _m)
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

    override def unapply(a: I, m: InterpModel[V, I]): Option[V] =
      m.eq get a map (_.head)
  }

  implicit def model[R, V, I](implicit imI: Interpretation[V, I, InterpModel[V, I]])
  : Interpretation[V, I, Model[R, V, I]] = new Interpretation[V, I, Model[R, V, I]] {
    override def apply(a: V, m: Model[R, V, I]): (I, Model[R, V, I]) = {
      val (aI, i2) = m.i interpretation a
      (aI, m.copy(i = i2))
    }

    override def unapply(a: I, m: Model[R, V, I]): Option[V] =
      m.i coimage a
  }

  // fixme: should this be against InterpModel rather than Model?
  implicit def opInterpolation[A[_], R, V, I]
  (implicit vOp: BinOp[A, V], iOp: BinOp[A, I], viI: Interpretation[V, I, Model[R, V, I]])
  : Interpretation[A[V], A[I], Model[R, V, I]] = new Interpretation[A[V], A[I], Model[R, V, I]]
  {
    override def apply(a: A[V], m0: Model[R, V, I]): (A[I], Model[R, V, I]) = {
      val (lhsV, rhsV) = vOp decompose a
      val (lhsI, m1) = m0 interpretation lhsV
      val (rhsI, m2) = m1 interpretation rhsV
      iOp.recompose(lhsI, rhsI) -> m2
    }

    override def unapply(a: A[I], m: Model[R, V, I]): Option[A[V]] = {
      val (lhsI, rhsI) = iOp decompose a
      for {
        lhsV <- m coimage lhsI
        rhsV <- m coimage rhsI
      } yield vOp.recompose(lhsV, rhsV)
    }
  }

  // fixme: should this be against InterpModel rather than Model?
  implicit def atInterpretation[R, V, I]
  (implicit viI: Interpretation[V, I, Model[R, V, I]])
  : Interpretation[AT[V], AT[I], Model[R, V, I]] = new Interpretation[AT[V], AT[I], Model[R, V, I]] {
    override def apply(a: AT[V], m0: Model[R, V, I]): (AT[I], Model[R, V, I]) = {
      val (pointI, m1) = m0 interpretation a.point
      AT(pointI, a.loc) -> m1
    }

    override def unapply(a: AT[I], m: Model[R, V, I]): Option[AT[V]] =
      m coimage a.point map (pV => AT(pV, a.loc))
  }
}


//trait Interpretations[I, M] {
//  def apply(m: M): TrueStream[I]
//}
//
//object Interpretations {
//
//  implicit class InterpretationsOps[M](val _m: M) {
//    def allInterpretations[I](implicit in: Interpretations[I, M]): TrueStream[I] =
//      in.apply(_m)
//  }
//
//  implicit def interpretations_interpModel[V, I]
//  : Interpretations[I, InterpModel[V, I]] = new Interpretations[I, InterpModel[V, I]] {
//    override def apply(m: InterpModel[V, I]): TrueStream[I] =
//      StreamT.fromStream(Need(m.eq.keys.to[Stream]))
//  }
//
//  implicit def interpretations_model[V, I]
//  : Interpretations[I, Model[V, I]] = new Interpretations[I, Model[V, I]] {
//    override def apply(m: Model[V, I]): TrueStream[I] =
//      m.i.allInterpretations
//  }
//
//}


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


trait Ranges[R, M] {
  def apply(m: M): TrueStream[R]
}

object Ranges {

  implicit class RangesOps[R, M](val _m: M) {
    def allRanges(implicit r: Ranges[R, M]): TrueStream[R] =
      r(_m)
  }

  implicit def modelRanges[R, V, I]: Ranges[R, Model[R, V, I]] = new Ranges[R, Model[R, V, I]] {
    override def apply(m: Model[R, V, I]): TrueStream[R] =
      m.str.allRanges
  }

  implicit def StrandModelRanges[R]: Ranges[R, StrandModel[R]] = new Ranges[R, StrandModel[R]] {
    override def apply(m: StrandModel[R]): TrueStream[R] =
      TrueStream(Set() ++ m.same_strand_as.map(_._1) ++ m.same_strand_as.map(_._2) ++ m.strand.keys)
  }
}