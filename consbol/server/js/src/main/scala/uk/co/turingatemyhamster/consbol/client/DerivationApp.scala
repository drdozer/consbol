package uk.co.turingatemyhamster.consbol.client

import org.scalajs.dom.html
import org.scalajs.jquery
import uk.co.turingatemyhamster.consbol.Derive.{DerivationResults, DProof}
import uk.co.turingatemyhamster.consbol._
import uk.co.turingatemyhamster.consbol.Tell.TellOps

import scala.scalajs.js
import scala.scalajs.js.Dynamic
import scala.scalajs.js.annotation.JSExport
import scalatags.JsDom.all._

import scalaz._
import Scalaz._

@JSExport("DerivationApp")
object DerivationApp {

  def unpack[A](dp: DProof[A]): Dynamic = {
    val u = dp.fold(unpackD, unpackP)
    Dynamic.global.console.dir(u)
    u
  }

  def unpackP[A](p: Proof[A]): Dynamic = {
    js.Dynamic.literal(
      label = s"[${p.goal}] ${p.name} ${p.cuts map (_.mkString(", ")) map (" | " + _) getOrElse ""}",
      icon = "proof",
      state = js.Dynamic.literal(
        opened = false,
        disabled = false,
        selected = false
      ),
      children = childrenOf(p)
    )
  }

  def unpackD[A](p: Disproof[A]): Dynamic = js.Dynamic.literal(
    label = s"[${p.goal}] (!) ${p.name} ${p.cuts map (_.mkString(", ")) map (" | " + _) getOrElse ""}",
    icon = "disproof",
    state = js.Dynamic.literal(
      opened = false,
      disabled = false,
      selected = false
    ),
    children = childrenOf(p)
  )

  def childrenOf[A](p: Proof[A]): js.Array[Any] =
    p match {
      case InterpretedProof(_, _, i) =>
        js.Array(unpackP(i))
      case Fact(_, _, _) =>
        js.Array("true")
      case Proof1(_, _, _, lhs) =>
        js.Array(unpackP(lhs))
      case Proof2(_, _, _, lhs, rhs) =>
        js.Array(unpackP(lhs), unpackP(rhs))
    }

  def childrenOf[A](p: Disproof[A]): js.Array[Any] =
    p match {
      case NoValue(_, _, _, value) =>
        js.Array(s"(!) $value")
      case FailureD(_, _, _) =>
        js.Array("(!) false")
      case InterpretedDisproof(_, _, i) =>
        js.Array(unpackD(i))
      case Cut(_, _, _) =>
        js.Array(s"(!) cut")
      case Disproof1(_, _, _, lhs) =>
        js.Array(unpackD(lhs))
      case Disproof2(_, _, _, lhs, rhs) =>
        js.Array(unpackP(lhs), unpackD(rhs))
    }

  @JSExport
  def render(to: html.Div): Unit = {
    val dm = DeriveRules.apply[Symbol, Symbol, String]
    val ds0 = DerivationState(env = DeriveEnv(dm), m0 = Model.empty[Symbol, Symbol, String])
    val ds1 = ds0 tell
      Strand('z, Orientation.+) tell
      DifferentStrandTo('y, 'z) tell
      SameStrandAs('y, 'x) tell
      SameStrandAs('w, 'x)

    import ds1.env._

    val res = derivation(DifferentStrandTo('x, 'z), ds1)
    val resL = res.take(50)
//    val res = derivation(Strand('x, Orientation.-), ds1)
    val dl = Dynamic.literal

    val failures = resL.takeWhile(_._1.isLeft)
    val theRest = resL.dropWhile(_._1.isLeft)
    val toFirstSuccess = failures mappend theRest.take(1)

    val x = js.Array(toFirstSuccess.map(r => unpack(r._1)).toStream.value :_*)
    val treeData = dl(
      data = x,
      autoOpen = false,
      dragAndDrop = false
    )

    Dynamic.global.console.dir(treeData)
    println(js.Dynamic.global.JSON.stringify(treeData))

    js.Dynamic.global.$(to).tree(
      treeData
    )

  }

  def derivation[A, R, V, I](a: A, m: DerivationState[R, V, I])(implicit d: Derive[A, R, V, I]) = d(a, m)
}
