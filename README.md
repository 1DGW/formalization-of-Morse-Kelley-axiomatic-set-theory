Axiomatic set theory is a foundational system of mathematics and has important applications in many fields. 
In this work, we present a formal system of axiomatic set theory based on the Coq proof assistant. 
The axiomatic system used in the formal system refers to Morse-Kelley (MK) set theory which is a relatively complete and concise axiomatic set theory.

Morse-Kelley set theory (MK) was first proposed by Wang ([DOI:10.1073/PNAS.35.3.150](https://www.pnas.org/doi/abs/10.1073/pnas.35.3.150)) in 1949
and was published as an appendix in Kelley’s *General Topology* in 1955.

MK includes eight axioms, one axiom schema, and 181 definitions or theorems. 
Different from ZFC, MK admits classes (whose quantity is more extensive than that of sets) as fundamental objects. 
That is to say, every mathematical object (ordered pair, function, integer, etc.) is a class, 
and only those classes belonging to some other ones are defined as sets. 
The non-set classes are named “proper classes”.
Monk, Rubin, and Mendelson submit that MK does what is expected of a set theory while being less cumbersome than ZFC.
In fact, ZFC can be proven consistent in MK[5]; MK is a proper extension of ZFC.
We consider that MK is a proper extension of ZFC and is convenient to utilize in formalization processes.

This is a repository optimized from our previous [version](https://github.com/styzystyzy/Axiomatic_Set_Theory/) with the main changes being:
- separating all the axioms and definitions of MK into one file (mk_structure.v) as its main structure;
- theorems along with their proofs into another file (mk_theorems.v) for easy lookup and calling.
