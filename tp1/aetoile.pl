%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

%
%Rappels sur l'algorithme
%
%- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
%- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
%
%   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
%   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
%   rapidement le prochain etat a developper (celui qui a f(U) minimum).
%
%   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
%   l'etat). Il permet de retrouver facilement n'importe quel etat pendant
%
%   On gere les 2 ensembles de facon synchronisee : chaque fois qu'on modifie
%   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.
%
%   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
%   facilement un etat par la donnee de sa situation.
%   Q est modelise par un seul arbre binaire de recherche equilibre.
%
%Predicat principal de l'algorithme :
%
%   aetoile(Pf,Pu,Q)
%
%   - reussit si Pf est vide ou bien contient un etat minimum terminal
%   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
%	 et pour chacun
%		si S appartient a Q, on l'oublie
%		si S appartient a Ps (etat deja rencontre), on compare
%			g(S)+h(S) avec la valeur deja calculee pour f(S)
%			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
%				g et f
%			sinon on ne touche pas a Pf
%		si S est entierement nouveau on l'insere dans Pf et dans Ps
%	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs
%

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q
	initial_state(S0),
	heuristique2(S0, H0),
	G0 is 0,
    F0 is H0 + G0,
    empty(Pf0),
    empty(Pu0),
    empty(Q0),
    insert([[F0, H0, G0], S0], Pf0, Pf1),
    insert([S0, [F0, H0, G0]], Pu0, Pu1),
	% lancement de Aetoile
    aetoile(Pf1, Pu1, Q0).

    % -------- UNIT TESTS --------

    % ----------------------------

test_loop_successors(Pf2, Pu2, Succs) :-
    initial_state(EtatInitial),
    final_state(EtatFinal),
    expand_all([[4,4,0], EtatInitial], Succs),
    empty(Pf0),
    empty(Pu0),
    empty(Q0),
    insert([[4,4,0], EtatInitial], Pf0, Pf1),
    insert([EtatInitial, [4,4,0]], Pu0, Pu1),
    loop_successors(Succs, Pf1, Pu1, Q0, Pf2, Pu2).

test_loop_suc_void :-
    loop_successors([], _,_,_,_,_).

test_loop_suc_in_Q :-
    initial_state(Ini),
    empty(Q),
    insert([Ini, [4,4,0]], Q, Q1),
    loop_successors([[[4,4,0], Ini]], _, _, Q1, _, _).


test_loop_suc_Pf1_Pf2_equals :-
    initial_state(Ini),
    empty(Q),
    expand_all(Ini, Succs),
    empty(Pf0),
    empty(Pu0),
    loop_successors(Succs, Pf1, Pu1, Q, Pf1, Pu1).


test_loop_suc_a_b_diff :-

    true.
%*******************************************************************************

expand([[_, _, G0], Etat], [[F, H, G], Suc], Step) :- % Succs avec tous les noeuds suivs et [F,G,H]
    follows(Etat, [Step, Suc], Poids),
    heuristique2(Suc, H),
    G is G0 + Poids,
    F is G + H.

expand_all(S, Succs) :-
    findall(T, expand(S, T, _), Succs).

% initial_state(Ini), expand_all(Ini, X).
test_expand :- initial_state(Ini), expand([[4,4,0], Ini], [[5, 4, 1], [[b, h, c], [a, vide, d], [g, f, e]]], _).
test_expand_all :-  initial_state(Ini), expand_all([[4,4,0], Ini], [[[5, 4, 1], [[b, h, c], [a, vide, d], [g, f, e]]]| _]).
%	suppress_min([[F0, H0, G0], Etat], Pf, Pf1),
%	suppress([Etat, _], Pu, Pu1),
%    follows(Etat, Follow),
%    heuristique2(Follow, H1),
%    G1 is G0 + 1,
%    F1 is G1 + H1.
%    findall([[F1, H1, G1], Etat], aetoile_step(Pf, Pu, Q, [[F1, H1, G1], Etat]), X),

% not in Q
loop_successors([[[F, H, G], S]| Succs], Pf, Pu, Q, Pf1, Pu1) :-
    belongs([S, _], Q), !,
    loop_successors(Succs, Pf, Pu, Q, Pf1, Pu1).


loop_successors([[[F, H, G], S]| Succs], Pf, Pu, Q, Pf3, Pu3) :-
    belongs([S, [F1,H1,G1]], Pu),
    F < F1,
    !,
    suppress([S, _], Pu, Pu1),
    insert([S, [F, H, G]], Pu1, Pu2),
    suppress([[F1, H1, G1], S], Pf, Pf1),
    insert([[F, H, G], S], Pf1, Pf2),
    loop_successors(Succs, Pf2, Pu2, Q, Pf3, Pu3).
    % s' = pop(S, Pu); if belongs then if s' better than S then insert s' esle insert S;

loop_successors([[_, S] | Succs], Pf, Pu, Q, Pf3, Pu3) :-
    belongs([S, _], Pu),
    !,
    loop_successors(Succs, Pf, Pu, Q, Pf3, Pu3).

% sinon (S est une situation nouvelle) il faut créer un nouveau terme à insérer dans Pu (idem dans Pf)
loop_successors([[[F, H, G], S]| Succs], Pf, Pu, Q, Pf2, Pu2) :-
    !,
    insert([S, [F, H, G]], Pu, Pu1),
    insert([[F, H, G], S], Pf, Pf1),
    loop_successors(Succs, Pf1, Pu1, Q, Pf2, Pu2).

% fin recurrence
loop_successors([], Pf, Pu, _, Pf, Pu) :- !.

aetoile(nil, nil, _) :- format("~w~n", ["PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE ! "]), !.

aetoile(Pf, _, _) :-
    suppress_min([_, MinState], Pf, _),
    final_state(MinState),
    !,
    affiche_solution(Pf).

aetoile(Pf, Pu, Q) :-
    suppress_min([[F0, H0, G0], Etat], Pf, Pf1),
    suppress([Etat, _], Pu, Pu1),
    expand_all([[F0,H0,G0], Etat], Succs),
    loop_successors(Succs, Pf1, Pu1, Q, Pf2, Pu2),
    insert([Etat, [F0, H0, G0]], Q, Q2),
    aetoile(Pf2, Pu2, Q2).




% Unit Test
%aetoile(nil, nil, _).

test :- empty(Pf0), final_state(Fin), insert([[0,0,0], Fin], Pf0, Pf1), aetoile(Pf1, _, _).

affiche_solution(nil):- format("~w~n", ["FIN"]), !.
affiche_solution(Avl):-
    suppress_min(Min, Avl, NewAvl),
    format("~w~n", [Min]),
    affiche_solution(NewAvl).

