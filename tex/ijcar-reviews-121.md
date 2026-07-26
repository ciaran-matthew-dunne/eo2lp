IJCAR'26 Paper #121 Reviews and Comments
===========================================================================
Paper #121 Automatically Translating Proof Systems for SMT Solvers to the
λΠ-calculus


Review #121A
===========================================================================

Overall merit
-------------
4. Accept

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
This paper presents the translation of the format Eunoia for proof systems to lambda-pi. There are not many challenges along the the way, but this is an important step for Eunoia (and to verify the correctness of the format).

Comments for authors
--------------------
- abstract: "proof systems of SMT solvers, namely cvc5" -> "of cvc5" would be more honnest
<!-- true. -->
- overall: Figure X, not "figure X"
<!--hmm. It depends on where the word 'figure' appears in a sentence. -->
- CPC-Mini is not introduced when it appears for the first time in the introduction (you have not talked about CPC)
<!-- TODO. -->
- "a distinctive feature of Eunoia": compared to what exactly?
<!-- as opposed to SMT-LIB and any other proof assistant I know of. -->
- in the experiments, I do not understand why you picked problems that are not in the fragment you support. Actually you specify that you "14 fragments covered by CPC-Mini", but later "CPC rules absent from CPC-Mini". Which one is it then?
<!-- TODO. check this. what are the failures caused by CPC rules absent from CPC-mini. QF_UFLIA? -->
- I am surprised that there is no evaluate rule like "2+3 = 5" (which I would expect to be important even if it is outside the Eunoia fragment)
<!-- there is an evaluate rule. `run_evaluate` in the main CPC file performs
these kinds of reductions on object-level expressions (and can be used within proofs???), 
and eo::add and eo::eq can perform this thing too, but this is the rule-specification level. -->

Also the paper is a paragraph too long.
<!-- error during submission. fixed. -->



Review #121B
===========================================================================

Overall merit
-------------
2. Weak reject

Reviewer expertise
------------------
4. Expert

Paper summary
-------------
This paper presents a translation from the Eunioa logical framework (used by CVC5 to represent its logic and theories and to export proofs) to lambdaPi modulo rewriting (used by the Dedukti group of systems for proof checking).
The translation is implemented and has been used to verify a large share of CVC5 proofs.

<!--thank you for the deep and extensive review. the comments are very useful. -->
Comments for authors
--------------------
I fully support the implementation work underlying this paper.
It is executed well, and the experimental results are convincing.
<!--thank you!-->
I suspect, if submitted as a system description, this paper would sail through easily.
Submitted as a regular paper, the case is murkier.

Eunoia and LambdaPi are both systems in the larger LF-family.
One could describe them as LF+A and LF+B, where A and B are the respective extensions made by the two systems.
A and B cover features like folding n-ary applications of binary operators, implicit arguments, and some kind of case-based computation.
<!--true. nice framing. -->
Consequently,
- it is not surprising that the translation is possible and relatively straightforward
- all the difficulty is in the details of matching A-features to B-features.
<!--true, but this is quite a lot of difficulty, given that the semantics of Eunoia is very much tied
 to the concrete syntax and ethos checker. and the way that eunoia handles variable binding (eo::lists of eo::vars), 
 dependent types (eo::quote), is very esoteric. -->

For better or worse, the translation is presented as concrete syntax to concrete syntax:
The paper gives the concrete grammars, with all idiosyncrasies for both systems, instead of the more common style of introducing abstract grammars for simplified languages.
<!--Eunoia has no abstract syntax. the shorthand given in section 2 is an attempt at getting something near to this. 
    The abstract syntax for lambdapi is already given in section 3 -- it is precisely the lambda-pi calculus modulo rewriting. 
    the concrete syntax for lambdapi just builds on top of that and the commands can just be seen as book-keeping
    the signature (`symbol`, `rule`, `require open`) and querying the type-checking relation (assert)  -->
Therefore, it has no feasible way of including the semantics of the systems and proving a meta-theorem that the translation is sound/complete.
But arguably, that is not important anyway: as the proofs get rechecked, the translation is barely part of the trusted code base, and extensive tests are available to flush out all bugs in the translation.
One might even say that focusing on the concrete syntax emphasizes that the translation is implemented and system-near.

I can't tell if this is an intentional choice of the authors, or the result of quickly writing a paper after implementing the translation.
<!--yes, it is intentional, since the -->
But either way, it occasionally harms readability because important details hide in a sea of low-level syntax.
This is especially for Eunoia's Lisp-like concrete syntax - expressions like "-> (eo::quote (=> F1 F2) (Proof G))" are awkward at best.
<!--yes, it would be nice to have an abstract syntax. but it seemed better to just directly show how we turn
  eo::quote types into dependent types by showing their lambdapi translation, rather than adding some special notation. -->
In multiple places, it is not easy to tell what the convoluted concrete syntax means intuitively, especially as the more idiosyncratic features are not given any more explanation than the standard ones.
<!-- we can fix this. more obvious explanations for eo::quote, eo::var, `:args` in proofs. -->
The focus on the concrete syntax also makes it hard to see how much of the difficulty stems only from the fact that both systems use very different concrete syntax but are very similar at the abstract syntax level, and where non-trivial encoding steps happen.
For example, a table listing all A-feautures abstractly and intuitively showing the corresponding B-representation, or a list of all corner cases where the translation is tricky would be a welcome complement.

Overall, I think this work should be published eventually.
I was going to go with score 3.
But when I realized how many of my minor comments were about something being unclear, I went down to 2.
I think it's better to give this paper one thorough revision and submit at the next opportunity.

----------Minor comments

always have page or line numbers when submitting

"Contribution": That paragraph reads more like overview

Fig. 2: The "s" clashes with the non-terminal s.

Section 2: This is awkward to read.
- Why introduce the concrete syntax if you're immediately abstracting a type system out of it?
- All the eo::... identifiers are too long and not well explained.
- parameter attributes are not explained when introduced
- What are f-lists?
- built-in symbols *\beta*
- quoted terms remain unclear

Section 2.1
- You're doing a lot here, but a lot is not clear and intuitive. You should give this section another go.
- The gray parts in the grammar witg are hard to read on a printout.
  I didn't even see the _* and _? on my first read.
- Eunoia's language is so simple that an experienced researcher should be able to figure out how it works by just looking at a commented grammar.
  But your grammar fails at that task. I was confused in multiple places.
- not immediately clear what macro definitions are because they are called differently in the grammar
- The :args was hard to understand

Section 3:
- Fig. 5, rule CON: Why is t:\mu checked? If t comes from \Sigma, it should be guaranteed to be well-typed.
- line 7: font of \Pi off
- line 7: delete "is some fresh variable that"
- Rem. 1, paranthesis: rephrase as "i.e., there are no expressions of type TYPE -> t"
- Rem. 1: identified with -> encoded as
- Rem. 1: Why are there two separate arrows for simple and dependent function types? The former is normally just an abbreviation for the latter.

Section 3.1:
- Why is there a syntax for LambdaPi in Fig. 6 and then a type system for a different syntax in Fig. 5?
- Fig. 6: lambdaPi is pretty simple. But like for Eunoia, your grammar has multiple parts that are hard to understand. That can be simplified.
- $ and @ and \zeta are unclear
- explanation of rewrite rule is unclear about whether single variables can be right-hand side
- validity of rewrite rules is defined, but there are no typing rules for them

Section 3.2:
- Def. 2: of_Z and of_Q are not explained
- "let" is not introduced
- What does eo::as do?
- Fig. 7: \phi is not explained

Section 4:
- Were heterogeneous lists mentioned before?
- You previously implied that translating at the framework level makes your approach more scalable.
  But now you still need a manually written prelude and to restrict to a "manageable" subset, which then checks in 0.1 seconds.
  I'm sure your implementation is good. But your explanation is confusing here.
- What are the restrictions (i) and (ii)?
- Would you be able to check more with a timeout about 5 seconds?
- Why does anything fail to check?
  Is your translation buggy?
   Are the terms too big for LambdaPi to handle?
   LambdaPi should check in linear time; so a large proof should be easily checkable by waiting long enough.
- Does your approach of encoding Eunoia in LambdaPi affect efficiency?
- Why do CPC rules cause typing errors? I thought you restricted to CPC-MINI.

Conclusion:
- exporting to other proof assistants via Dedukti:
  I understand why you mention that. But I'm skeptical.
  I suspect the more realistic use case would be to adapt your tool to import straight from CVC5 than to go via Dedukti.
- a thorough comparison with Ethos: You should at least sketch it here.



Review #121C
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
4. Expert

Paper summary
-------------
The paper presents a translation of the Eunoia logical framework to the λΠ
calculus modulo rewriting, implemented in the LambdaPi proof assistant. A
notable aspect of the translation is that it targets Eunoia itself, not a
specific proof system. This makes the translation in principle universal
for any proof system definable in Eunoia. 

Eunoia allows users to define proof rules as well as declarative, purely
functional programs that, in essence, can be used to implement operational
side conditions for those rules. The presented translation leverages the
rewriting features of that λΠ calculus to enable the translation of Eunoia
programs to rewrite rules. Other challenges for the translation, such as 
the lack of polymorphism in λΠ are addressed in a standard way.

The translation has been implemented in OCaml and used for an experimental
valuation described in the paper. For that, the authors have focused on a
subset of the CPC calculus -- the proof system used by the cvc5 SMT solver 
to produce proof certificates. The experiment suggests that cvc5 proofs
in that sub-calculus can be translated and checked by LambdaPi rather
efficiently with very high coverage. 
If the translator were extensible to the full CPC calculus with similar
performance results, the combination of the translator and LambdaPi would 
constitute a viable alternative proof checker for cvc5 proofs.

Comments for authors
--------------------
The work is very interesting and is described with remarkable clarity and 
conciseness. This includes the introductions to Eunoia, the λΠ calculus 
modulo rewriting and the LambdaPi assistant. Readers not familiar with
Eunoia and λΠ might find the presentation a bit terse since much of the
notation is not explained, although it is mostly intuitive for people 
familiar with work on proof assistants. 

Based on the paper's description of Eunoia, the translation seems quite
natural and reasonable, although I wish the author has commented more on 
its design, especially with regards to some of the more peculiar aspects 
of Eunoia such as the eo:quote operator or the weakness of the type system
for side-condition programs.

Overall, the work seems solid, promising and worth publishing at IJCAR. 
There are, however, a couple of issues that prevent me from giving it a
stronger score. I list them below and hope they can be addressed by the
authors in their rebuttal. 

1. The abstract is potentially misleading as it suggests that the paper 
presents a full translation of Eunoia. However, program sublanguage pf
Eunoia's has a very large number of builtin operators. It is not clear how
many of them are supported by the translation. This should be addressed.

2. Presently there is no publicly available formal semantics of Eunoia. 
Its only description is an informal one in the online user manual of the 
Ethos checker. Since the authors are not among the Eunoia developers, nor 
do they acknowledge in the paper any conversations with them on Einoia’s 
semantics, it is unclear how accurate the presented translation to LambaPi 
is, or will be after publication. Given that, as stated by its own 
developers, the language is not yet stable and is still evolving, it makes
one wonder whether this submission is premature.
Put another way, it would be good to understand what evidence the authors 
have that their translation is faithful to the intended semantics of 
Eunoia. 

Minor comments:

* I find it strange that you present the fully automated translation of 
mini- CPC in this work in contraposition to the "manual" translation 
achieved in lean-SMT. That one too is fully automated. What is not automated 
is the proof of soundness of its rules. In the lean-SMT work, the rules 
have been proven sound manually (or, rather, interactively) in Lean. In 
your work, you state you have no proofs at all in LambdaPi yet.

* You want to check the grammar of lines 10 and -1 on page 1.
