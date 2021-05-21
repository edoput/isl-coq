Page 2: forall -> for all, use colon in front of Hoare triple, and punctuation in the next sentence.
Page 2 last sentence: an -> a
Page 3: the -> then, forall -> for all
Page 3: use more punctuation
Page 5: ot -> it
Page 5: extra the

General comments:
- Use a bit more punctuation
- Go over the document with a spell checker
- Try to write a bit more concisely and to-the-point

For example, the first paragraph of chapter 2:
+ You emphasize (italics) words that are not relevant to your thesis.
+ Why is this paragraph in the chapter about operational semantics, instead of introduction?
+ If the setting is that the programmer already has an erroring execution, why do incorrectness logic?


How about something like this, in the intro:
+ Given a program, we can assert {P} somewhere in the program, which means that whenever execution hits that point, then predicate P holds.
+ We can prove this formally using Hoare triples: we put such a {P} between every two lines in our program, and if {P} e {P'} is a valid Hoare triple for every line e, then all the {P}'s have been formally proved.
+ Dually, we can put [P] somewhere in program, which means that for every state satisfying P, there exists an execution hitting that state at [P].
+ We can use incorrectness triples to formally prove this, analogous to Hoare triples.
+ The point of incorrectness logic is that an automatic tool can use it to search for bugs.
+ Your thesis is about formally verifying the rules of incorrectness logic in Coq.

Then this info is out of the way, and in subsequent chapters you can focus on the technical details, instead of re-motivating what you're talking about.

An example paragraph from chapter 2:

> Using the error expression is possible to report errors when executing the program, as an example consider the case of unchecked division n / m, while we would like it to be total and always return an expression this is not possible in the case of n / 0 because it has no meaning. Checking for this condition and returning the error expression then solves this.
> The following example would be the check for a checked-division function that takes two natural numbers n, m and computes the result of n / m safely as it can check that the divisor m is not zero and raise an error in case it is.
> if m == 0 then
>    error
> When using the manual memory management expressions [...]


I think you first need to describe that you need a formal concept of error to be able to do incorrectness logic. Then you can explain how errors occur using load and store. Then you can rewrite the paragraph above as:

"""
The `error` expression can be used to manually signal an error when the language would not otherwise do so. For example, our division operator silently gives n/0 = 0 for division by zero. We can define safe division that manually signals an error:

  safe_div(n,m) := if m == 0 then error else n / m

Thus, use of the `error` expression enables Hoare logic and incorrectness logic to reason about new classes of errors defined by the programmer.
"""

Page 10: Be more explicit that you model errors as stuck states. You do say this later on page 12, but it's nice to have that up front.
Page 10: reduce -> reduces

Page 15: What is v*?

Page 15-16: The discussion of predicate logic vs separation logic is a bit confusing. IMO it is clearer to talk about predicates over heaps from the start. Maybe you can split it up into three parts:
1. Ordinary predicate logic, where you explicitly write predicates over heaps h, e.g. P(h) := (h(x) = v) ∧ (h(y) = w) ∧ (x ≠ y).
2. Predicate logic with a points to connective: P := (x ↦ v) ∧ (y ↦ w) ∧ (x ≠ y); we interpret each connective as a predicate over heaps, e.g. (P ∧ Q)(h) = P(h) ∧ Q(h).
3. Separation logic connectives: P := (x ↦ v) ∗ (y ↦ w)

Chapter 3 explains what has already been explained in chapter 2.

Page 22: The reflexive transitive closure of step has already been defined previously.

Page 22: The more intuitive description of definition 6 can be interpreted incorrectly. It currently reads as for all states in P, but it should say exists.

Page 23: Triple comes out into the margin. Maybe use \[ \].

Page 24: I think strongest post deserves its own section.

Page 24: Duplicate explanation of incorrectness triples.

Page 24: Unfinished sentence at the bottom.

Page 25: I don't understand figure 4.3. The claim seems to make does not seem to type check.

Page 25: You first explain incorrectness triples, then post, and then you give incorrectness triple rules. I think it's better to completely describe triples first, then completely describe post.

Page 29-32: I think this section should match what you actually did in Coq.

