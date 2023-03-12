	/*
	Une situation est decrite par une matrice 3x3.
	Chaque case est soit un emplacement libre (Variable LIBRE), soit contient le symbole d'un des 2 joueurs (o ou x)

	Contrairement a la convention du tp precedent, pour modeliser une case libre
	dans une matrice on n'utilise pas une constante speciale (ex : nil, 'vide', 'libre','inoccupee' ...);
	On utilise plut�t un identificateur de variable, qui n'est pas unifiee (ex : X, A, ... ou _) .
	La situation initiale est une "matrice" 3x3 (liste de 3 listes de 3 termes chacune)
	o� chaque terme est une variable libre.
	Chaque coup d'un des 2 joureurs consiste a donner une valeur (symbole x ou o) a une case libre de la grille
	et non a deplacer des symboles deja presents sur la grille.

	Pour placer un symbole dans une grille S1, il suffit d'unifier une des variables encore libres de la matrice S1,
	soit en ecrivant directement Case=o ou Case=x, ou bien en accedant a cette case avec les predicats member, nth1, ...
	La grille S1 a change d'etat, mais on n'a pas besoin de 2 arguments representant la grille avant et apres le coup,
	un seul suffit.
	Ainsi si on joue un coup en S, S perd une variable libre, mais peut continuer a s'appeler S (on n'a pas besoin de la designer
	par un nouvel identificateur).
	*/

:- use_module(library(clpfd)).

situation_initiale([ [_,_,_],
                     [_,_,_],
                     [_,_,_] ]).

	% Convention (arbitraire) : c'est x qui commence

joueur_initial(x).


	% Definition de la relation adversaire/2

adversaire(x,o).
adversaire(o,x).


	/*
	 DEFINIR ICI a l'aide du predicat ground/1 comment
	 reconnaitre une situation terminale dans laquelle il
	 n'y a aucun emplacement libre : aucun joueur ne peut
	 continuer a jouer (quel qu'il soit).
	 ****************************************************/

% situation_terminale(_Joueur, Situation) :-   ? ? ? ? ?

	/*
	DEFINITIONS D'UN ALIGNEMENT
	***************************/

alignement(L, Matrix) :- ligne(    L,Matrix).
alignement(C, Matrix) :- colonne(  C,Matrix).
alignement(D, Matrix) :- diagonale(D,Matrix).

	/*
	 DEFINIR ICI chaque type d'alignement maximal
 	 existant dans une matrice carree NxN.
	 ********************************************/

ligne(L, M) :- nth1(_, M, L).


colonne(C,M) :-
        transpose(M, MT),
        nth1(_, MT, C).


	/* Definition de la relation liant une diagonale D a la matrice M dans laquelle elle se trouve.
		il y en a 2 sortes de diagonales dans une matrice carree(https://fr.wikipedia.org/wiki/Diagonale) :
		- la premiere diagonale (principale)  : (A I)
		- la seconde diagonale                : (Z R)
		A . . . . . . . Z
		. \ . . . . . / .
		. . \ . . . / . .
		. . . \ . / . . .
		. . . . X . . .
		. . . / . \ . . .
		. . / . . . \ . .
		. / . . . . . \ .
		R . . . . . . . I
	*/

diagonale(D, M) :-
	premiere_diag(1,D,M).

diagonale(D, M) :-
    seconde_diag(1,D,M).


premiere_diag(_,[],[]).
% K is num de colonne, E c'est la ligne
premiere_diag(K,[E|D],[Ligne|M]) :-
	nth1(K,Ligne,E),
	K1 is K+1,
	premiere_diag(K1,D,M).

seconde_diag(_,[],[]).
seconde_diag(K,[E|D],[Ligne|M]) :-
    reverse(Ligne,Ligne1),
    nth1(K, Ligne1, E),
    K1 is K+1,
    seconde_diag(K1,D,M).

	/*
	 DEFINITION D'UN ALIGNEMENT
	 POSSIBLE POUR UN JOUEUR DONNE
	 *****************************/

possible([X|L], J) :- unifiable(X,J), possible(L,J).
possible(  [],  _).

	/* Attention
	il faut juste verifier le caractere unifiable
	de chaque emplacement de la liste, mais il ne
	faut pas realiser l'unification.
	*/
unifiable(X,J) :- X = J.
unifiable(X,_) :- var(X).

	/*
	 DEFINITION D'UN ALIGNEMENT GAGNANT
	 OU PERDANT POUR UN JOUEUR DONNE J
	 **********************************/
	/*
	Un alignement gagnant pour J est un alignement
possible pour J qui n'a aucun element encore libre.
	*/

	/*
	Remarque : le predicat ground(X) permet de verifier qu'un terme
	prolog quelconque ne contient aucune partie variable (libre).
	exemples :
		?- ground(Var).
		no
		?- ground([1,2]).
		yes
		?- ground(toto(nil)).
		yes
		?- ground( [1, toto(nil), foo(a,B,c)] ).
		no
	*/

	/* Un alignement perdant pour J est un alignement gagnant pour son adversaire. */


alignement_gagnant([], _).
alignement_gagnant([X|R], J) :-
    ground([X|R]),
    X = J,
    alignement_gagnant(R, J).

% alignement_gagnant([[x,x,x],[x,x,x],[x,x,x]],x).

test_alignement_gagnant :-
    alignement_gagnant([x,x,x],x),
    not(alignement_gagnant([x,_,x],x)),
    not(alignement_gagnant([x,x,o],x)).

alignement_perdant([], _).
alignement_perdant([X|R], J) :-
    ground([X|R]),
    adversaire(J, EJ),
    X = EJ,
    alignement_perdant(R,J).

test_alignement_perdant :-
        not(alignement_perdant([x,x,x],x)),
        not(alignement_perdant([x,_,x],x)),
        alignement_perdant([o,o,o],x).

	/* ****************************
	DEFINITION D'UN ETAT SUCCESSEUR
	****************************** */

	/*
	Il faut definir quelle operation subit la matrice
	M representant l'Etat courant
	lorsqu'un joueur J joue en coordonnees [L,C]
	*/

successeur(J, Etat,[L,C]) :-
    nth1(L,Etat,Lig),
    nth1(C,Lig,J).

% situation_initiale(S), successeur(x,S,[1,1]), X=S.


	/*
   	 EVALUATION HEURISTIQUE D'UNE SITUATION
  	 **************************************/

	/*
	1/ l'heuristique est +infini si la situation J est gagnante pour J
	2/ l'heuristique est -infini si la situation J est perdante pour J
	3/ sinon, on fait la difference entre :
	   le nombre d'alignements possibles pour J
	moins
 	   le nombre d'alignements possibles pour l'adversaire de J
*/


heuristique(J,Situation,H) :-		% cas 1
   H = 10000,				% grand nombre approximant +infini
   alignement(Alig,Situation),
   alignement_gagnant(Alig,J), !.

heuristique(J,Situation,H) :-		% cas 2
   H = -10000,				% grand nombre approximant -infini
   alignement(Alig,Situation),
   alignement_perdant(Alig,J), !.


% on ne vient ici que si les cut precedents n'ont pas fonctionne,
% c-a-d si Situation n'est ni perdante ni gagnante.
heuristique(J, Situation, H) :-
    findall(Alig, (alignement(Alig,Situation),possible(Alig, J)), G),
    findall(Alig, (alignement(Alig,Situation),adversaire(J,A), possible(Alig, A)), GA),
    length(G, Glg),
    length(GA, Glga),
    H is Glg - Glga.

%  M = [[x,_,_], [x,o,o], [_,o,o]], heuristique(x, M, H).
%  M = [[x,_,_], [x,_,o], [_,o,o]], heuristique(o, M, H).
% findall(Alig, (alignement(Alig,M),possible(Alig, J)), X).
% M = [[x,_,_], [x,_,o], [_,o,o]], findall(Alig, (alignement(Alig,M),possible(Alig, J)), X), length(X, L).
