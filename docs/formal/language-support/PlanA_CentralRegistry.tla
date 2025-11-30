--------------------------- MODULE PlanA_CentralRegistry ---------------------------
(*
 * Plan A: Central Registry + Thin Abstraction
 * TLA+ behavioral specification for language analyzer locking protocol
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Languages,      \* Set of supported languages (e.g., {"ts", "swift", "php"})
    Files,          \* Set of file identifiers
    Analyzers       \* Set of analyzer identifiers

VARIABLES
    \* @type: Str -> Str;
    registry,       \* Function: Language -> Analyzer (or NULL)
    \* @type: Str -> Str;
    fileLang,       \* Function: File -> Language
    \* @type: Str -> Str;
    fileLock,       \* Function: File -> Analyzer (or NULL)
    \* @type: Str -> Str;
    analyzerLang    \* Function: Analyzer -> Language

vars == <<registry, fileLang, fileLock, analyzerLang>>

NULL == CHOOSE n : n \notin (Languages \union Files \union Analyzers)

TypeOK ==
    /\ registry \in [Languages -> Analyzers \union {NULL}]
    /\ fileLang \in [Files -> Languages]
    /\ fileLock \in [Files -> Analyzers \union {NULL}]
    /\ analyzerLang \in [Analyzers -> Languages]

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ registry = [l \in Languages |-> NULL]
    /\ fileLang \in [Files -> Languages]  \* Non-deterministic assignment
    /\ fileLock = [f \in Files |-> NULL]
    /\ analyzerLang \in [Analyzers -> Languages]

-----------------------------------------------------------------------------
(* Actions *)

(* Register an analyzer for a language *)
RegisterAnalyzer(a, l) ==
    /\ analyzerLang[a] = l              \* Analyzer supports this language
    /\ registry[l] = NULL               \* No analyzer registered yet
    /\ registry' = [registry EXCEPT ![l] = a]
    /\ UNCHANGED <<fileLang, fileLock, analyzerLang>>

(* Lock a file for analysis *)
LockFile(f, a) ==
    /\ fileLock[f] = NULL               \* File not locked
    /\ analyzerLang[a] = fileLang[f]    \* Language match required
    /\ registry[fileLang[f]] = a        \* Must be the registered analyzer
    /\ fileLock' = [fileLock EXCEPT ![f] = a]
    /\ UNCHANGED <<registry, fileLang, analyzerLang>>

(* Unlock a file after analysis *)
UnlockFile(f) ==
    /\ fileLock[f] # NULL               \* File is locked
    /\ fileLock' = [fileLock EXCEPT ![f] = NULL]
    /\ UNCHANGED <<registry, fileLang, analyzerLang>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E a \in Analyzers, l \in Languages : RegisterAnalyzer(a, l)
    \/ \E f \in Files, a \in Analyzers : LockFile(f, a)
    \/ \E f \in Files : UnlockFile(f)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

(* A file can only be locked by at most one analyzer *)
MutualExclusion ==
    \A f \in Files : Cardinality({a \in Analyzers : fileLock[f] = a}) <= 1

(* A locked file's analyzer must support its language *)
LockLanguageConsistency ==
    \A f \in Files :
        fileLock[f] # NULL => analyzerLang[fileLock[f]] = fileLang[f]

(* Each language has at most one registered analyzer *)
RegistryUniqueness ==
    \A l \in Languages : Cardinality({a \in Analyzers : registry[l] = a}) <= 1

(* A locked file must be locked by the registered analyzer for its language *)
LockRegistryConsistency ==
    \A f \in Files :
        fileLock[f] # NULL => registry[fileLang[f]] = fileLock[f]

-----------------------------------------------------------------------------
(* Combined Invariant *)

Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ LockLanguageConsistency
    /\ RegistryUniqueness
    /\ LockRegistryConsistency

=============================================================================
