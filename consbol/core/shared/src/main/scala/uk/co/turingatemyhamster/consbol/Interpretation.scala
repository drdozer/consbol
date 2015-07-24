package uk.co.turingatemyhamster.consbol

import scala.language.higherKinds
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

  implicit def dsInterpretation[TV, TI, R, V, I]
  (implicit mi: Interpretation[TV, TI, Model[R, V, I]])
  : Interpretation[TV, TI, DerivationState[R, V, I]] = new Interpretation[TV, TI, DerivationState[R, V, I]] {
    override def unapply(a: TI, ds0: DerivationState[R, V, I]): Option[TV] =
      ds0.m0 coimage a

    override def apply(a: TV, ds0: DerivationState[R, V, I]): (TI, DerivationState[R, V, I]) = {
      val (ti, m1) = ds0.m0 interpretation a
      ti -> (ds0 withModel m1)
    }
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

  implicit def binOpInterpolation[A[_], R, V, I]
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

  implicit def monOpInterpretation[A[_], X, R, V, I]
  (implicit vOp: MonOp[A, V, X], iOp: MonOp[A, I, X], viI: Interpretation[V, I, Model[R, V, I]])
  : Interpretation[A[V], A[I], Model[R, V, I]] = new Interpretation[A[V], A[I], Model[R, V, I]] {
    override def apply(a: A[V], m0: Model[R, V, I]): (A[I], Model[R, V, I]) = {
      val (lhsV, x) = vOp decompose a
      val (lhsI, m1) = m0 interpretation lhsV
      iOp.recompose(lhsI, x) -> m1
    }

    override def unapply(a: A[I], m: Model[R, V, I]): Option[A[V]] = {
      val (lhsI, x) = iOp decompose a
      for {
        lhsV <- m coimage lhsI
      } yield vOp.recompose(lhsV, x)
    }
  }

  implicit def monOp2Interpretation[A[_, _], X, Y, R, V, I]
  (implicit vOp: MonOp2[A, R, V, X], iOp: MonOp2[A, R, I, Y], viX: Interpretation[X, Y, Model[R, V, I]])
  : Interpretation[A[R, V], A[R, I], Model[R, V, I]] = new Interpretation[A[R, V], A[R, I], Model[R, V, I]]
  {
    override def unapply(a: A[R, I], m: Model[R, V, I]): Option[A[R, V]] = {
      val (r, y) = iOp.decompose(a)
      for {
        x <- viX.unapply(y, m)
      } yield vOp.recompose(r, x)
    }

    override def apply(a: A[R, V], m0: Model[R, V, I]): (A[R, I], Model[R, V, I]) = {
      val (r, x) = vOp.decompose(a)
      val (y, m1) = viX(x, m0)
      iOp.recompose(r, y) -> m1
    }
  }

  implicit def pairInterpretation[X, Y, M](implicit i: Interpretation[X, Y, M])
  : Interpretation[(X, X), (Y, Y), M] = new Interpretation[(X, X), (Y, Y), M]
  {
    override def unapply(a: (Y, Y), m: M): Option[(X, X)] = {
      for {
        x1 <- i.unapply(a._1, m)
        x2 <- i.unapply(a._2, m)
      } yield (x1, x2)
    }

    override def apply(a: (X, X), m: M): ((Y, Y), M) = {
      val (y1, m1) = i(a._1, m)
      val (y2, m2) = i(a._2, m1)
      (y1, y2) -> m2
    }
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


trait Atoms[T, M] {
  def apply(m: M): TrueStream[T]
}

object Atoms {

  implicit class AtomsOps[T, M](val _m: M) {
    def all(implicit r: Atoms[T, M]): TrueStream[T] =
      r(_m)
  }

  implicit def derivationStateRanges[T, R, V, I]
  (implicit mr: Atoms[T, Model[R, V, I]])
  : Atoms[T, DerivationState[R, V, I]] = new Atoms[T, DerivationState[R, V, I]] {
    override def apply(m: DerivationState[R, V, I]): TrueStream[T] =
      m.m0.all
  }

  implicit def modelRanges[R, V, I]
  (implicit sr: Atoms[R, StrandModel[R]])
  : Atoms[R, Model[R, V, I]] = new Atoms[R, Model[R, V, I]] {
    override def apply(m: Model[R, V, I]): TrueStream[R] =
      m.str.all
  }

  implicit def StrandModelRanges[R]: Atoms[R, StrandModel[R]] = new Atoms[R, StrandModel[R]] {
    override def apply(m: StrandModel[R]): TrueStream[R] =
      TrueStream(Set() ++ m.same_strand_as.map(_._1) ++ m.same_strand_as.map(_._2) ++ m.strand.keys)
  }

  implicit def modelIndexes[R, V, I]
  (implicit sr: Atoms[I, InterpModel[V, I]])
  : Atoms[I, Model[R, V, I]] = new Atoms[I, Model[R, V, I]] {
    override def apply(m: Model[R, V, I]): TrueStream[I] =
      m.i.all
  }

  implicit def InterpretationModelIndexes[V, I]: Atoms[I, InterpModel[V, I]] = new Atoms[I, InterpModel[V, I]] {
    override def apply(m: InterpModel[V, I]): TrueStream[I] =
      TrueStream(m.eq.keySet)
  }
}