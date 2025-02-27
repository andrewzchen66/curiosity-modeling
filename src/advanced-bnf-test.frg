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
    `IfExp.then_expr = `Exp2
    // `IfExp.else_expr = `Exp3
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
    `IfExp.then_expr = `IfExp
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
    `IfExp.then_expr = `Exp1
    `IfExp.else_expr = `Exp1
  }
}

test suite for validLetExp {
  example validLetExp_good is {validLetExp} for {
    BaseExp = `LetExp + `Exp1 + `Exp2
    Exp = `LetExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    LetExp = `LetExp
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
    `LetExp.bind_expr = `Exp1
    `LetExp.body_expr = `Exp2
  }

  example validLetExp_bad_self_ref is {not validLetExp} for {
    BaseExp = `LetExp + `Exp1 + `Exp2
    Exp = `LetExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    LetExp = `LetExp
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
    `LetExp.bind_expr = `LetExp
    `LetExp.body_expr = `LetExp
  }

  example validLetExp_bad_shared_branch is {not validLetExp} for {
    BaseExp = `LetExp + `Exp1 + `Exp2
    Exp = `LetExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    LetExp = `LetExp
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
    `LetExp.bind_expr = `Exp1
    `LetExp.body_expr = `Exp1
  }
}

test suite for expReachable {
  example validExpReachable is {{some expr1, expr2: Exp | expReachable[expr1, expr2]}} for {
    BaseExp = `LetExp + `Exp1 + `Exp2
    Exp = `LetExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    LetExp = `LetExp
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
    `LetExp.bind_expr = `Exp1
    `LetExp.body_expr = `Exp2
  }

  example validExpReachable2 is {{some expr1, expr2: Exp | expReachable[expr1, expr2]}} for {
    BaseExp = `Exp1
    Exp = `Exp1 + `Infix11 + `Infix21 + `Term1

    SeqExp = `Exp1
    Infix1 = `Infix11
    Infix2 = `Infix21
    Term = `Term1
    `Term1.n = 1

    `Infix11.infix2 = `Infix21
    `Infix21.term = `Term1
    `Exp1.infix1 = `Infix11
  }

  example invalidExpReachable is {{some expr1, expr2: Exp | not expReachable[expr1, expr2]}} for {
    BaseExp = `LetExp + `Exp1 + `Exp2
    Exp = `LetExp + `Exp1 + `Exp2 + `Infix11 + `Infix12 + `Infix21 + `Infix22 + `Term1 + `Term2

    LetExp = `LetExp
    SeqExp = `Exp1 + `Exp2
    Infix1 = `Infix11 + `Infix12
    Infix2 = `Infix21 + `Infix22
    Term = `Term1 + `Term2
    `Term1.n = 1
    `Term2.n = 2
  }
}

test suite for noDangling {
  example noDangling_true is {noDangling} for {
    Program = `Program
    Exp = `BaseExp
    BaseExp = `BaseExp
    `Program.program_expr = `BaseExp
  }

  example noDangling_false is {not noDangling} for {
    Program = `Program
    Exp = `BaseExp1 + `BaseExp2
    BaseExp = `BaseExp1 + `BaseExp2
    `Program.program_expr = `BaseExp1
  }
}

test suite for noExpCycles {
  example noExpCycles_true is {noExpCycles} for {
    Exp = `LetExp + `IfExp + `SeqExp
    BaseExp = `LetExp + `IfExp + `SeqExp
    LetExp = `LetExp
    `LetExp.bind_expr = `SeqExp
    `IfExp.if_expr = `SeqExp
  }

  example noExpCycles_false is {not noExpCycles} for {
    Exp = `LetExp + `IfExp
    BaseExp = `LetExp + `IfExp
    LetExp = `LetExp
    IfExp = `IfExp
    `LetExp.bind_expr = `IfExp
    `IfExp.if_expr = `LetExp
  }
}

test suite for noExpDAGs {
  example noExpDAGs_true is {noExpDAGs} for {
    Exp = `Term1 + `Term2
    `Term1.n = 1
    `Term2.n = 2
  }

  example noExpDAGs_false is {not noExpDAGs} for {
    Exp = `LetExp + `IfExp + `SeqExp
    BaseExp = `LetExp + `IfExp + `SeqExp
    LetExp = `LetExp
    `LetExp.bind_expr = `SeqExp
    `IfExp.if_expr = `SeqExp
  }
}
