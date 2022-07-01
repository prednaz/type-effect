Authors: Philipp Zander (7983034), Samuel Klumpers (6057314)

In this project we implemented Control Flow Analysis for the Fun language, by extending algorithm W to track annotations.
We augment the Fun language with pairs, lists, and general datatypes, and provide new rules for the annotations in these cases.
We furthermore extend the Control Flow Analysis to Call Tracking Analysis by inserting \texttt{\&} effects for calls into the rules, and implement subtyping to replace subeffecting.
