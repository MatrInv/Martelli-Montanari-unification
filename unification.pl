
:- dynamic(echo/1). %Prédicat nécessaire au fonctionnement de echo

:- op(20,xfy,?=). %Def de l opérateur ?=



%----- Def Unification -----%


unifie(P, premier) :- choix_premier(P, E, R), echo(system : P), echo(+ R : E), reduit(R,E,P,Q), unifie(Q, premier) , !.
unifie(P, pondere) :- choix_pondere(P, E, R), echo(system : P), echo(+ R : E), reduit(R,E,P,Q), unifie(Q, pondere) , !.
unifie([],_).

trace_unif(P,S) :- set_echo, unifie(P,S).

unif(P,S) :- clr_echo, unifie(P,S).



%----- Def de la fonction de Choix Premier -----%


choix_premier([X|_], X, R) :- regle(X,R) .



%----- Def de la fonction de Choix Pondéré -----%


choix_pondere(L, E, R) :- (choix_CC(L, E, R); choix_RS(L, E, R); choix_O(L, E, R); choix_D(L, E, R); choix_E(L, E, R)), !.


choix_CC([X|_], X, R) :- (regle(X, checkR); regle(X, clashR)), regle(X, R) .
choix_CC([X|L], E, R) :- \+regle(X, clashR), \+regle(X, checkR), choix_CC(L, E, R) .

choix_RS([X|_], X, R) :- (regle(X, renameR); regle(X, simplifyR)), regle(X, R) .
choix_RS([X|L], E, R) :- \+regle(X, renameR), \+regle(X, simplifyR), choix_RS(L, E, R) .

choix_O([X|_], X, R) :- regle(X, orientR), regle(X, R) .
choix_O([X|L], E, R) :- \+regle(X, orientR), choix_O(L, E, R) .

choix_D([X|_], X, R) :- regle(X, decomposeR), regle(X, R) .
choix_D([X|L], E, R) :- \+regle(X, decomposeR), choix_D(L, E, R) .

choix_E([X|_], X, R) :- regle(X, expandR), regle(X, R) .
choix_E([X|L], E, R) :- \+regle(X, expandR), choix_E(L, E, R) .



%----- Def des conditions sur les règles -----%


regle(T?=X,orientR) :- var(X), nonvar(T), !.

regle(X?=T,decomposeR) :- nonvar(X), nonvar(T), functor(X,Nx,Ax), functor(T,Nt,At), Nx==Nt, Ax=:=At, !.

regle(X?=T,simplifyR) :- var(X), const(T), !.

regle(X?=T,expandR) :- var(X), nonvar(T), functor(T,_,A), A>0, \+ occur_check(X,T), !.

regle(X?=T,renameR) :- var(X), var(T), !.

regle(X?=T,checkR) :- var(X), nonvar(T), functor(T,_,A), A>0, X \== T, occur_check(X,T), !.

regle(X?=T,clashR) :- nonvar(X), nonvar(T), functor(X,Nx,Ax), functor(T,Nt,At), (Nx\==Nt; Ax=\=At), !.



%----- Def des transformations associées aux regles -----%


reduit(orientR, T?=X, P, [X?=T|Q]) :- suppr(T?=X,P,Q) .

reduit(decomposeR, X?=T, P, Q) :- X=..[_|ListeX], T=..[_|ListeT], dec(ListeX, ListeT, ListeSortie), suppr(X?=T, P, Pp), append(Pp, ListeSortie, Q), ! . 

reduit(simplifyR, X?=T, P, Q) :- suppr(X?=T, P, Q), X=T, ! .

reduit(expandR, X?=T, P, Q) :- suppr(X?=T, P, Q), X=T, ! .

reduit(renameR, X?=T, P, Q) :- suppr(X?=T, P, Q), X=T, ! .

reduit(checkR, _, _, bottom) .

reduit(clashR, _, _, bottom) .



%----- Def des fonctions intermediaires -----%


occur_check(X,T) :- term_variables(T,L) , occur_check_list(X,L).

occur_check_list(X, [Y|L]) :- \+ same_term(X,Y), occur_check_list(X, L).
occur_check_list(X, [Y|_]) :- same_term(X,Y).

const(X) :- nonvar(X), functor(X,_,A), A=:=0.

dec([A|X], [B|T], [A ?= B | Q]) :- dec(X, T, Q) .
dec([], [], []).

suppr(E,[X|L],Sout) :- X\==E, append([X],Q,Sout), suppr(E,L,Q).
suppr(E,[X|L],Sout)	:- X==E, append([],L,Sout).
suppr(_,[],[]).



%----- Def des fonctions d affichage -----%


% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.
echo(T) :- echo_on, !, writeln(T) .
echo(_).

% set_echo: ce prédicat active l affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l affichage par le prédicat echo
clr_echo :- retractall(echo_on).