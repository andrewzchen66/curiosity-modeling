# curiosity-modeling

## Project Objective

Compilers and Interpreters usually contain an initial parsing step that turns a program (which abstractly is just a really long string) into an Abstract Syntax Tree. To define the rules that determine whether a program's syntax is valid or not, the parser uses BNF (Backus-Naur Form)-- a formal notation to precisely define the syntax of a programming language-- during the parsing step to turn the "flat" string into a tree representation. In this project, we model a simple BNF in Forge as a proof of concept for modeling the space of all possible programs in a language. Our inspiration stems from a curiosity of creating our own programming languages, with the hope that this tool can be used to ensure valid syntax and wellformedness.

## Model Design and Visualization:

The following is an example of a simple bnf that we model in simple-bnf.frg:

<s_exp> ::=
| NUM (n)
| SYM (s)
| LPAREN <lst> RPAREN

<lst> ::=
| ε
| <s_exp> <lst>

The angle-bracketed keywords are referred to as nonterminals. They don't exist in the program string directly but are useful for splitting up our grammar into parsable chunks. Each "|" delimiter represents a production rule, representing all the valid forms that the corresponding nonterminal should adhere to in order to be syntactically valid. The other symbols such as NUM, SYM, and ε (Empty) represent terminals which should exist from the program string directly. A more complicated bnf example that we have partially modeled in advanced-bnf.frg can be found in advanced-bnf.txt.

As our end goal is to visualize an Abstract Syntax Tree, we found that the default visualization is suitable for accurately depicting our model. To read the output of an instance, it is typically enough to look at the leaf nodes (terminals) sequentially to work out the initial program that is being represented. The root node should always be a Program, and the remaining internal nodes should represent nonterminals.

Our main run statement validates various properties of the AST, such as no dangling Expressions, no cycles or DAGs, and the valid If and Let Exps.

## Signatures and Predicates

At a high level, we model all nonterminals as empty sigs, and model terminals as sigs that extend the abstract sig Exp. For example, the BaseExp sig represents the <expr> terminal, and each production rule for <expr> is another abstract class that inherits BaseExp. The terminals are represented as fields within these nonterminal sigs, for example the sig PlusInfix2\_ has a field of type one PLUS. This format allows the model to represent BNF's grammar in a nested, tree-like structure.

We also implemented various predicates:

- expReachable[expr1, expr2]: Ensures that every expression in the tree is reachable from another expression.
- noDangling[program]: Ensures that no expressions are dangling and all are part of the main program.
- noExpCycles: Prevents cyclic dependencies in expressions.
- noExpDAGs: Ensures that each expression has at most one parent, avoiding directed acyclic graphs (DAGs).
- validIfExp: Enforces that if_expr and else_expr are distinct and do not reference the containing expression.
- validLetExp: Ensures that bind_expr and body_expr are distinct and do not reference the containing expression.

## Testing

What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.
