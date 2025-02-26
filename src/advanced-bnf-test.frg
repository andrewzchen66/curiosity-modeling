#lang forge/froglet
open "advanced-bnf.frg"

test suite for validIfExp {
  example validIfExp_good is {validIfExp} for {
    BaseExp = `IfExp + `Exp1 + `Exp2
    Exp = `IfExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    IfExp = `IfExp
    SeqExp = `Exp1 + `Exp2
    Infix1 = `Infix11 + `Infix12
    Infix2 = `Infix21 + `Infix22
    Term = `Term1 + `Term2
    `Term1.n = 1
    `Term2.n = 2

    `Infix11.infix2 = `Infix21
    `Infix12.infix2 = `Infix22
    `Infix21.term = `Term1
    `Infix22.term = `Term2
    `Exp1.infix1 = `Infix11
    `Exp2.infix1 = `Infix12
    `IfExp.if_expr = `Exp1
    `IfExp.else_expr = `Exp2
  }

  example validIfExp_bad_self_ref is {not validIfExp} for {
    BaseExp = `IfExp + `Exp1 + `Exp2
    Exp = `IfExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    IfExp = `IfExp
    SeqExp = `Exp1 + `Exp2
    Infix1 = `Infix11 + `Infix12
    Infix2 = `Infix21 + `Infix22
    Term = `Term1 + `Term2
    `Term1.n = 1
    `Term2.n = 2

    `Infix11.infix2 = `Infix21
    `Infix12.infix2 = `Infix22
    `Infix21.term = `Term1
    `Infix22.term = `Term2
    `Exp1.infix1 = `Infix11
    `Exp2.infix1 = `Infix12
    `IfExp.if_expr = `IfExp
    `IfExp.else_expr = `IfExp
  }

  example validIfExp_bad_shared_branch is {not validIfExp} for {
    BaseExp = `IfExp + `Exp1 + `Exp2
    Exp = `IfExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    IfExp = `IfExp
    SeqExp = `Exp1 + `Exp2
    Infix1 = `Infix11 + `Infix12
    Infix2 = `Infix21 + `Infix22
    Term = `Term1 + `Term2
    `Term1.n = 1
    `Term2.n = 2

    `Infix11.infix2 = `Infix21
    `Infix12.infix2 = `Infix22
    `Infix21.term = `Term1
    `Infix22.term = `Term2
    `Exp1.infix1 = `Infix11
    `Exp2.infix1 = `Infix12
    `IfExp.if_expr = `Exp1
    `IfExp.else_expr = `Exp1
  }
}

test suite for validLetExp {

}