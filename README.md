# Évaluateur et Typeur pour Lambda-Calcul

Merouane BOUAFIA

## Description

Ce projet implémente un évaluateur et un typeur pour un lambda-calcul simplement typé étendu avec :
- **Calcul lambda** : variables, abstractions, applications
- **Arithmétique** : entiers naturels, addition, soustraction
- **Listes** : construction, déconstruction (head, tail), tests
- **Conditionnelles** : `ifzero`, `ifempty`
- **Point fixe** : récursion via `fix`
- **Let-bindings** : liaisons locales
- **Traits impératifs** : références mutables, déréférencement, affectation
- **Polymorphisme faible** : pour la sûreté du typage avec références

## Comment exécuter

### Compilation
```bash
ocamlc -o ast ast.ml
```

### Exécution
```bash
./ast
```

Le programme affichera automatiquement les résultats d'inférence de types et d'évaluation pour des exemples définis.

---

## Types de Données

### `pterm` - Termes du langage

Représente les expressions du lambda-calcul.

#### Constructeurs :

- **`Var of string`** : Variable
  
- **`App of pterm * pterm`** : Application d'une fonction
  
- **`Abs of string * pterm`** : Abstraction (fonction anonyme)
  
- **`N of int`** : Constante entière
  
- **`Add of pterm * pterm`** : Addition
  
- **`Sub of pterm * pterm`** : Soustraction
  
- **`Nil`** : Liste vide
  
- **`Cons of pterm * pterm`** : Construction de liste (tête :: queue)
  
- **`Hd of pterm`** : Tête d'une liste
  
- **`Tl of pterm`** : Queue d'une liste
  
- **`IfZero of pterm * pterm * pterm`** : Conditionnelle sur zéro
  
- **`IfEmpty of pterm * pterm * pterm`** : Conditionnelle sur liste vide
  
- **`Fix of pterm`** : Point fixe pour la récursion
  
- **`Let of string * pterm * pterm`** : Liaison locale
  
- **`Unit`** : Valeur unité (pour effets de bord)
  
- **`Ref of pterm`** : Création d'une référence mutable
  
- **`Deref of pterm`** : Déréférencement d'une référence
  
- **`Assign of pterm * pterm`** : Affectation mutable
  
- **`Loc of int`** : Adresse mémoire (utilisée en interne pendant l'évaluation)
  
---

### `ptype` - Types

Représente les types du système de types.

#### Constructeurs :

- **`TVar of string`** : Variable de type (polymorphique)
  
- **`PolyFaible of string`** : Variable de type polymorphe faible
  
- **`Arr of ptype * ptype`** : Type fonction (flèche)
  
- **`Nat`** : Type des entiers naturels

- **`List of ptype`** : Type liste
  
- **`Forall of string list * ptype`** : Quantification universelle
  
- **`TUnit`** : Type unité

- **`TRef of ptype`** : Type référence
  
---

### `env` - Environnement de typage

```ocaml
type env = (string * ptype) list
```

Associe des variables à leurs types. Utilisé pendant l'inférence de types.

---

### `equa` - Équations de typage

```ocaml
type equa = (ptype * ptype) list
```

Liste de contraintes d'égalité entre types, générées pendant l'inférence et résolues par unification.

---

### `state` - État mémoire

```ocaml
type state = (int * pterm) list
```

Associe des adresses mémoire (`int`) à des valeurs (`pterm`). Utilisé pour l'évaluation des références mutables.

---

## Fonctions Principales

### Pretty Printing

#### `print_term : pterm -> string`

Convertit un terme en chaîne de caractères à afficher.

#### `print_type : ptype -> string`

Convertit un type en chaîne de caractères à afficher.

---

### Génération de Variables Fraîches

#### `nouvelle_var : unit -> string`

Génère un nouveau nom de variable.

#### `nouvelle_var_term : unit -> string`

Génère un nouveau nom de terme.

#### `nouvelle_region : unit -> int`

Génère une nouvelle adresse mémoire pour les références.

---

### Inférence de Types

#### `cherche_type : string -> env -> ptype`

Recherche le type d'une variable dans l'environnement de typage.
**Renvoie :** `VarPasTrouve` si la variable n'est pas dans l'environnement.

#### `appartient_type : string -> ptype -> bool`

Vérifie si une variable de type apparaît dans un type
Utilisé dans l'unification pour éviter les types infinis.

#### `substitue_type : ptype -> string -> ptype -> ptype`

Remplace une variable de type par un type dans un type donné.

#### `substitue_type_partout : equa -> string -> ptype -> equa`

Applique une substitution de type à toutes les équations.

#### `is_non_expansive : pterm -> bool`

Détermine si une expression est non-expansive (valeur).

**Non-expansif :** `Var`, `Abs`, `N`, `Nil`, `Unit`, `Cons` de valeurs
**Expansif :** `App`, `Add`, `Sub`, `Ref`, `Deref`, `Assign`, `Fix`, etc.

**Utilisé pour :** Le polymorphisme faible - les expressions expansives reçoivent des types `PolyFaible`.

#### `genere_equa : pterm -> ptype -> env -> equa`

Génère les contraintes de typage pour un terme.

**Algorithme :** Parcourt récursivement le terme et génère des équations entre types.

#### `unification : equa_zip -> string -> ptype`

Résout un système d'équations de types par unification.

**Algorithme de résolution de termes :**
1. Décompose les types structurés (flèches, listes, références)
2. Substitue les variables de type
3. Vérifie l'occurrence pour éviter les types infinis
4. Gère les variables faibles (`PolyFaible`)

**Renvoie :**  `Echec_unif` si les types sont incompatibles.

#### `inference : pterm -> string`

Fonction principale d'inférence de types.

**Processus :**
1. Génère les équations avec `genere_equa`
2. Résout par unification
3. Retourne le type inféré ou un message d'erreur

---

### Évaluation

#### `free_vars : pterm -> string list`

Calcule l'ensemble des variables libres d'un terme.

#### `rename_bound : pterm -> string -> string -> pterm`

Renomme les occurrences libres d'une variable dans un terme.
Utilisé dans la substitution avec capture-avoiding.

#### `subst : pterm -> string -> pterm -> pterm`

Substitution avec évitement de capture : `t[v := s]`

#### `is_value : pterm -> bool`

Détermine si un terme est une valeur.

**Valeurs :** `Abs`, `N`, `Nil`, `Cons` de valeurs, `Unit`, `Loc`

#### `lookup_state : state -> int -> pterm option`

Recherche la valeur stockée à une adresse mémoire.
**Renvoie :** `Some valeur` si trouvée, `None` sinon.

#### `update_state : state -> int -> pterm -> state`

Met à jour l'état mémoire à une adresse donnée.

#### `eval1_with_state : pterm -> state -> (pterm * state) option`

Effectue une étape de réduction avec gestion de l'état mémoire.

**Règles principales :**
- **β-réduction :** `(λx.e) v` → `e[x := v]` (si `v` est une valeur)
- **Addition :** `n1 + n2` → `n1+n2`
- **Soustraction :** `n1 - n2` → `n1-n2`
- **Hd :** `hd (v1 :: v2)` → `v1`
- **Tl :** `tl (v1 :: v2)` → `v2`
- **IfZero :** `ifzero 0 then e1 else e2` → `e1`
- **IfEmpty :** `ifempty [] then e1 else e2` → `e1`
- **Fix :** `fix (λf.e)` → `e[f := fix (λf.e)]`
- **Let :** `let x = v in e` → `e[x := v]` (si `v` est une valeur)
- **Ref :** `ref v` → `loc r` (alloue une nouvelle région `r`)
- **Deref :** `!loc r` → `v` (lit la valeur à l'adresse `r`)
- **Assign :** `loc r := v` → `()` (écrit `v` à l'adresse `r`)

**Renvoie :** `Some (terme_réduit, nouvel_état)` ou `None` si bloqué.

#### `eval : ?max_steps:int -> pterm -> pterm`

Évalue un terme jusqu'à sa forme normale.

**Paramètres :**
- `max_steps` : Limite d'étapes (par défaut: 10000) pour éviter les boucles infinies

**Renvoie :** `Divergence` si la limite est atteinte.

#### `eval_to_string : ?max_steps:int -> pterm -> string`

Évalue et affiche le résultat sous forme de chaîne.

**Format :** `"terme ==> résultat"`

---

## Polymorphisme Faible

Le polymorphisme faible est implémenté pour garantir la sûreté du typage avec les références mutables.

### Principe

**Expression non-expansive** : Valeur syntaxique (variable, constante, abstraction, liste de valeurs)
→ Type polymorphique avec `TVar`

**Expression expansive** : Calcul potentiel (application, `ref`, opération)
→ Type faible avec `PolyFaible`

### Pourquoi ?

Sans polymorphisme faible, ce programme dangereux serait accepté :
```ocaml
let l = ref [] in
let _ = l := [fun x -> x] in
(hd !l) + 2
```

**Problème :** `ref []` aurait le type `∀a. a list ref`, permettant de stocker une fonction puis de l'utiliser comme entier !

**Solution :** `ref []` reçoit le type faible `'a list ref`, qui ne peut pas être généralisé.

### Exemples

**Accepté (polymorphisme complet) :**
```ocaml
let l = [] in
let l1 = 1 :: l in
let l2 = (fun x -> x) :: l in
()
```
`l` a le type `∀a. [a]` car `[]` est non-expansif.

**Rejeté (polymorphisme faible) :**
```ocaml
let l = ref [] in
let _ = l := [fun x -> x] in
(hd !l) + 2
```
`l` a le type `'a list ref` (type faible), donc l'unification échoue entre `Nat -> Nat` et `Nat`.

---

## Exceptions

- **`VarPasTrouve`** : Variable non trouvée dans l'environnement
- **`TypingError of string`** : Erreur de typage (ex: `fix` sans abstraction)
- **`Echec_unif of string`** : Échec d'unification (types incompatibles)
- **`EvalStuck of string`** : Évaluation bloquée (terme non-réductible, non-valeur)
- **`Divergence of string`** : Dépassement de la limite d'étapes

---

## Structure du Code

1. **Définitions des types** : `pterm`, `ptype`, `env`, `equa`, `state`
2. **Pretty printing** : `print_term`, `print_type`
3. **Inférence de types** :
   - Génération de variables fraîches
   - Manipulation de types
   - Génération d'équations
   - Unification
4. **Exemples de typage** : Nombreux exemples couvrant toutes les constructions
5. **Évaluation** :
   - Variables libres et substitution
   - Prédicat de valeur
   - Gestion de l'état mémoire
   - Réduction avec état
6. **Exemples d'évaluation** : Tests de toutes les fonctionnalités
7. **Tests du polymorphisme faible** : Exemples acceptés et rejetés
8. **Fonction main** : Exécute tous les exemples

---

## Exemples d'Utilisation

### Lambda-calcul de base
```ocaml
let ex_id = Abs ("x", Var "x")
(* Type inféré : T1 -> T1 *)

let ex_k = Abs ("x", Abs ("y", Var "x"))
(* Type inféré : (T1 -> (T2 -> T1)) *)
```

### Arithmétique
```ocaml
let ex_nat1 = App (Abs ("x", Add (Var "x", N 1)), N 3)
(* Type : Nat, Évalue à : 4 *)
```

### Listes
```ocaml
let ex_list = Cons (N 1, Cons (N 2, Nil))
(* Type : [Nat], Évalue à : (1 :: (2 :: [])) *)
```

### Récursion
```ocaml
let ex_fact = Fix (Abs ("f", Abs ("n", 
  IfZero (Var "n", N 1, 
    Add (Var "n", App (Var "f", Sub (Var "n", N 1)))))))
(* Calcule la factorielle *)
```

### Références mutables
```ocaml
let ex_ref = Let ("r", Ref (N 5),
                  Let ("_", Assign (Var "r", N 10),
                      Deref (Var "r")))
(* Type : Nat, Évalue à : 10 *)
```

---