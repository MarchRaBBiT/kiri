--------------------------- MODULE PlanC_Capability ---------------------------
(*
 * Plan C: Capability-based Composition
 * TLA+ behavioral specification for capability composition protocol
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Languages,          \* Set of supported languages
    Files,              \* Set of file identifiers
    Capabilities,       \* Set of capabilities (e.g., {"symbol", "type", "doc"})
    RequiredCaps        \* Minimum required capabilities (e.g., {"symbol"})

VARIABLES
    providers,          \* Function: ProviderId -> {lang, caps}
    analyzers,          \* Function: AnalyzerId -> {lang, providers}
    fileLang,           \* Function: File -> Language
    fileLock            \* Function: File -> AnalyzerId (or NULL)

vars == <<providers, analyzers, fileLang, fileLock>>

NULL == CHOOSE n : n \notin (Languages \union Files \union Capabilities)

ProviderIds == 1..5
AnalyzerIds == 1..3

TypeOK ==
    /\ providers \in [ProviderIds -> [lang: Languages, caps: SUBSET Capabilities] \union {NULL}]
    /\ analyzers \in [AnalyzerIds -> [lang: Languages, provs: SUBSET ProviderIds] \union {NULL}]
    /\ fileLang \in [Files -> Languages]
    /\ fileLock \in [Files -> AnalyzerIds \union {NULL}]

-----------------------------------------------------------------------------
(* Helper: Get capabilities of an analyzer *)
AnalyzerCaps(a) ==
    IF analyzers[a] = NULL
    THEN {}
    ELSE UNION {providers[p].caps : p \in analyzers[a].provs}

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ providers = [p \in ProviderIds |-> NULL]
    /\ analyzers = [a \in AnalyzerIds |-> NULL]
    /\ fileLang \in [Files -> Languages]
    /\ fileLock = [f \in Files |-> NULL]

-----------------------------------------------------------------------------
(* Actions *)

(* Create a capability provider *)
CreateProvider(p, l, caps) ==
    /\ providers[p] = NULL
    /\ caps # {}
    /\ providers' = [providers EXCEPT ![p] = [lang |-> l, caps |-> caps]]
    /\ UNCHANGED <<analyzers, fileLang, fileLock>>

(* Compose an analyzer from providers *)
ComposeAnalyzer(a, l, provs) ==
    /\ analyzers[a] = NULL
    /\ provs # {}
    /\ \A p \in provs : providers[p] # NULL /\ providers[p].lang = l
    \* Must include required capabilities
    /\ RequiredCaps \subseteq UNION {providers[p].caps : p \in provs}
    /\ analyzers' = [analyzers EXCEPT ![a] = [lang |-> l, provs |-> provs]]
    /\ UNCHANGED <<providers, fileLang, fileLock>>

(* Lock a file with a composed analyzer *)
LockFile(f, a) ==
    /\ fileLock[f] = NULL
    /\ analyzers[a] # NULL
    /\ analyzers[a].lang = fileLang[f]
    /\ fileLock' = [fileLock EXCEPT ![f] = a]
    /\ UNCHANGED <<providers, analyzers, fileLang>>

(* Unlock a file *)
UnlockFile(f) ==
    /\ fileLock[f] # NULL
    /\ fileLock' = [fileLock EXCEPT ![f] = NULL]
    /\ UNCHANGED <<providers, analyzers, fileLang>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E p \in ProviderIds, l \in Languages, caps \in SUBSET Capabilities :
        caps # {} /\ CreateProvider(p, l, caps)
    \/ \E a \in AnalyzerIds, l \in Languages, provs \in SUBSET ProviderIds :
        provs # {} /\ ComposeAnalyzer(a, l, provs)
    \/ \E f \in Files, a \in AnalyzerIds : LockFile(f, a)
    \/ \E f \in Files : UnlockFile(f)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

(* Every analyzer has required capabilities *)
MinimumCapabilities ==
    \A a \in AnalyzerIds :
        analyzers[a] # NULL => RequiredCaps \subseteq AnalyzerCaps(a)

(* Provider language matches analyzer language *)
ProviderLanguageMatch ==
    \A a \in AnalyzerIds :
        analyzers[a] # NULL =>
            \A p \in analyzers[a].provs :
                providers[p] # NULL /\ providers[p].lang = analyzers[a].lang

(* Lock language consistency *)
LockLanguageConsistency ==
    \A f \in Files :
        fileLock[f] # NULL =>
            analyzers[fileLock[f]] # NULL /\
            analyzers[fileLock[f]].lang = fileLang[f]

(* Mutual exclusion *)
MutualExclusion ==
    \A f \in Files : Cardinality({a \in AnalyzerIds : fileLock[f] = a}) <= 1

(* Capability traceability *)
CapabilityTraceability ==
    \A a \in AnalyzerIds, c \in Capabilities :
        (analyzers[a] # NULL /\ c \in AnalyzerCaps(a)) =>
            \E p \in analyzers[a].provs : c \in providers[p].caps

-----------------------------------------------------------------------------
(* Combined Invariant *)

Invariant ==
    /\ TypeOK
    /\ MinimumCapabilities
    /\ ProviderLanguageMatch
    /\ LockLanguageConsistency
    /\ MutualExclusion
    /\ CapabilityTraceability

=============================================================================
