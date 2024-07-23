# Morse-Kelley Axiomatic Set Theory
Axiomatic set theory is a foundational system of mathematics and has important applications in many fields. 
In this work, we present a formal system of axiomatic set theory based on the Coq proof assistant. 
The axiomatic system used in the formal system refers to Morse-Kelley (MK) set theory which is a relatively complete and concise axiomatic set theory.

Morse-Kelley set theory (MK) was first proposed by Wang ([DOI:10.1073/PNAS.35.3.150](https://www.pnas.org/doi/abs/10.1073/pnas.35.3.150)) in 1949
and was published as the appendix in Kelley’s *General Topology* in 1955.

MK includes eight axioms, one axiom schema, and 181 definitions or theorems. 
Different from ZFC, MK admits classes (whose quantity is more extensive than that of sets) as fundamental objects. 
That is to say, every mathematical object (ordered pair, function, integer, etc.) is a class, 
and only those classes belonging to some other ones are defined as sets. 
The non-set classes are named “proper classes”.
Monk, Rubin, and Mendelson submit that MK does what is expected of a set theory while being less cumbersome than ZFC.
In fact, ZFC can be proven consistent in MK.
We consider that MK is a proper extension of ZFC and is convenient to utilize in formalization processes.

# Files
The formalization is guided by the appendix in Kelley’s *General Topology* publishe in 1955,
where the entire axioms, definitions and theorems of Morse-Kelley \(MK\) axiomatic set theory were introduced.
The formalization consists of two \(.v\)files:

mk_structure.v  --  the formalization of all the definitions and axioms of MK.

mk_theorems.v  --  the formalization and verification of all the theorems in MK.

**Note**: mk_theorems.v is dependent upon mk_structure.v

# Authors
This project is implemented by Wensheng Yu<wsyu@bupt.edu.cn>, Tianyu sun, Yaoshun Fu, Dakai Guo, Si Chen, Qimeng Zhang and Guowei Dou<dgw@bupt.edu.cn>.

Beijing Key Laboratory of Space-ground Interconnection and Convergence, School of Electronic Engineering, Beijing University of Posts and Telecommunications, Beijing

# Relevant Papers & Books
\[1\] Yu, W., Sun, T., Fu, Y.: A Machine Proof System for Axiomatic Set Theory (in Chinese). Science Press, Beijing (2020)

\[2\] Sun, T., Yu, W.: A formal system of axiomatic set theory in Coq. IEEE Access. 8, 21510-21523 (2020) [DOI: 10.1109/ACCESS.2020.2969486](https://doi.org/10.1109/ACCESS.2020.2969486)

This project is optimized from our previous [version](https://github.com/styzystyzy/Axiomatic_Set_Theory/) (presented in \[2\]) with the main changes being:
- separating all the axioms and definitions of MK into one file (mk_structure.v) as its main structure;
- theorems along with their proofs into another file (mk_theorems.v) for easy lookup and calling.
