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

@JSExport("DerivationApp")
object DerivationApp {

  def unpack[A](dp: DProof[A]): Dynamic = {
    println(s"Unpacking $dp")
    dp.fold(unpackD, unpackP)
  }

  def unpackP[A](p: Proof[A]): Dynamic = {
    println(s"unpackP for $p")
    js.Dynamic.literal(
      label = s"${p.name} ${p.goal}",
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
    label = s"${p.name} ${p.goal}",
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
      case InterpretedProof(_, i) =>
        js.Array(unpackP(i))
      case Fact(_) =>
        js.Array("fact")
      case Proof1(_, _, lhs) =>
        js.Array(unpackP(lhs))
      case Proof2(_, _, lhs, rhs) =>
        println(s"Unpacking $lhs and $rhs")
        js.Array(unpackP(lhs), unpackP(rhs))
    }

  def childrenOf[A](p: Disproof[A]): js.Array[Any] =
    p match {
      case InterpretedDisproof(_, i) =>
        js.Array(unpackD(i))
      case Cut(_, _, lhs) =>
        js.Array(unpackD(lhs))
      case Disproof1(_, _, lhs) =>
        js.Array(unpack(lhs))
      case Disproof2(_, _, lhs, rhs) =>
        js.Array(unpack(lhs), unpack(rhs))
    }

  @JSExport
  def render(to: html.Div): Unit = {
    val ds0 = DerivationState(m0 = Model.empty[Symbol, Symbol, String])
    val ds1 = ds0 tell
      Strand('u, Orientation.+) tell
      DifferentStrandTo('t, 'u) tell
      SameStrandAs('t, 's) tell
      SameStrandAs('s, 'r)

    val a = Strand('r, Orientation.-)
    val d = implicitly[Derive[Strand[Symbol], Model[Symbol, Symbol, String]]]

    val res = d.apply(a, ds1)
    val dl = Dynamic.literal

    val x = js.Array(res.map(r => unpack(r._1)).toStream.value :_*)
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
}
