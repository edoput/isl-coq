\section{Introduction}

\section{The Coq project in english \& math \& inference rules with horizontal line \& examples (15 pages)}

\subsection{Operational semantics}
\subsection{The top level goal, definition of a crash}
\subsection{Definition of separation logic}
\subsection{Definition of post}
\subsection{Post rules}
\subsection{Definition of hoare}
\subsection{Hoare rules}

\section{Section of what it looks like in Coq (shorter: 3-5 pages)}

\section{Concurrency, but maybe only a description of what the difficulties are and some initial progress}

\section{Conclusion}


k => (if amb == 3 then crash else 8)
-------------------------------------
k => crash

apply (amb_step 3) ==>

k => (if 3 == 3 then crash else 8)
-------------------------------------
k => crash

apply eq_step ==>

k => (if true then crash else 8)
-------------------------------------
k => crash

apply true_step ==>

k => crash
-------------------------------------
k => crash

eauto.



v ↦ 0
k => while(true){ v := v+1 }
l => if(v == 3){crash}else{return 3}
-------------------------------------
∃ t, t => crash

step k a few times:

v ↦ 3
k => while(true){ v := v+1 }
l => if(v == 3){crash}else{return 3}
-------------------------------------
∃ t, t => crash

step l:

v ↦ 3
k => while(true){ v := v+1 }
l => if(3 == 3){crash}else{return 3}
-------------------------------------
∃ t, t => crash

step l again:

v ↦ 3
k => while(true){ v := v+1 }
l => crash
-------------------------------------
∃ t, t => crash


Lemma. for all m:

v ↦ n
k => while(true){ v := v+1 }
-∗
v ↦ n+m
k => while(true){ v := v+1 }


post e .. := ... (1 => e) ...

Ideas:
1. We decide which thread steps, and what step it takes if there is more than one possible step (e.g. if we have amb).
2. We can also have abstraction in this setting, simply by proving lemma's: incorrectness triples are just lemma's.

Question:
1. If we have the setup like that, does it completely subsume incorrectness logic?
2. Can we make a logic like that in Coq, that actually works like that?
3. Maybe we can implement this logic simply by doing ordinary incorrectness logic for a language with a thread pool?
    Instead of a single expression we have a thread pool: a map from integers to exprs.
    We have an operational semantics that says something like:
    <threadpool, heap> ~> <threadpool',heap'>
    ...
    post ({k ↦ e, l ↦ e'})