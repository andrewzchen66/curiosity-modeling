# curiosity-modeling

As part of your project submission, we request a one page README.md file that provides a comprehensive overview of your implementation. This document should effectively communicate your approach and insights to someone who might be new to your chosen topic. At a minimum, you should address each of the following points:

## Project Objective

What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

Compilers and Interpreters usually contain an initial parsing step that turns a program (which abstractly is just a really long string) into an Abstract Syntax Tree. To define the rules that determine whether a program's syntax is valid or not, the parser uses BNF (Backus-Naur Form)-- a formal notation to precisely define the syntax of a programming language-- during the parsing step to turn the "flat" string into a tree representation. In this project, we model a simple BNF in Forge as a proof of concept for modeling the space of all possible programs in a language. Our inspiration stems from a curiosity of creating our own programming languages, with the hope that this tool can be used to ensure valid syntax and wellformedness.

## Model Design and Visualization:

Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

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

## Signatures and Predicates

At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

## Testing

What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

# Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.

Your README.md should not only serve as a guide to your project but also reflect your understanding and the thought process behind your modeling decisions.
