package uk.co.turingatemyhamster.consbol.util

import scala.annotation.tailrec
import scala.language.experimental.macros

case class FuncName(name: String, fullName: String)

object Utils {
  implicit def enclosingFunctionName: FuncName = macro funcNameImpl

  def funcNameImpl(c: Compat.Context): c.Expr[FuncName] = {
    import c.universe._

    @tailrec def walkSymbols(sym: c.Symbol): c.Expr[FuncName] = {
      val simpleName = sym.name.decoded.toString.trim
      val fullName = sym.fullName.trim

      if(simpleName startsWith "$") {
        walkSymbols(sym.owner)
      } else {
        val name = q"$simpleName"
        c.Expr[FuncName](q"uk.co.turingatemyhamster.consbol.util.FuncName($name, $fullName)")
      }
    }

    val sym = Compat.enclosingName(c)
    walkSymbols(sym.asInstanceOf[c.Symbol])
  }
}

object Compat{
  type Context = scala.reflect.macros.blackbox.Context
  def enclosingName(c: Context) = {
    c.internal.enclosingOwner
  }
}