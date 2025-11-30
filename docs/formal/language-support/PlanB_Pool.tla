--------------------------- MODULE PlanB_Pool ---------------------------
(*
 * Plan B: Hierarchical Backend + Pool Integration
 * TLA+ behavioral specification for pooled client locking protocol
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    Languages,      \* Set of supported languages
    Files,          \* Set of file identifiers
    MaxPoolSize     \* Maximum clients per pool

VARIABLES
    pool,           \* Function: Language -> Sequence of {state, id}
    fileLang,       \* Function: File -> Language
    fileLock,       \* Function: File -> ClientId (or NULL)
    clientState     \* Function: ClientId -> {"available", "in_use", "failed"}

vars == <<pool, fileLang, fileLock, clientState>>

NULL == CHOOSE n : n \notin (Languages \union Files)

ClientIds == 1..10  \* Pool of client IDs

TypeOK ==
    /\ \A l \in Languages : pool[l] \subseteq ClientIds
    /\ fileLang \in [Files -> Languages]
    /\ fileLock \in [Files -> ClientIds \union {NULL}]
    /\ clientState \in [ClientIds -> {"available", "in_use", "failed", "unused"}]

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ pool = [l \in Languages |-> {}]
    /\ fileLang \in [Files -> Languages]
    /\ fileLock = [f \in Files |-> NULL]
    /\ clientState = [c \in ClientIds |-> "unused"]

-----------------------------------------------------------------------------
(* Actions *)

(* Add a client to a language pool *)
AddClientToPool(l, c) ==
    /\ clientState[c] = "unused"
    /\ Cardinality(pool[l]) < MaxPoolSize
    /\ pool' = [pool EXCEPT ![l] = pool[l] \union {c}]
    /\ clientState' = [clientState EXCEPT ![c] = "available"]
    /\ UNCHANGED <<fileLang, fileLock>>

(* Acquire a client from pool to lock a file *)
AcquireClient(f, c) ==
    /\ fileLock[f] = NULL
    /\ c \in pool[fileLang[f]]
    /\ clientState[c] = "available"
    /\ clientState' = [clientState EXCEPT ![c] = "in_use"]
    /\ fileLock' = [fileLock EXCEPT ![f] = c]
    /\ UNCHANGED <<pool, fileLang>>

(* Release a client back to pool *)
ReleaseClient(f) ==
    /\ fileLock[f] # NULL
    /\ LET c == fileLock[f] IN
        /\ clientState' = [clientState EXCEPT ![c] = "available"]
        /\ fileLock' = [fileLock EXCEPT ![f] = NULL]
    /\ UNCHANGED <<pool, fileLang>>

(* Client failure *)
ClientFails(c) ==
    /\ clientState[c] \in {"available", "in_use"}
    /\ clientState' = [clientState EXCEPT ![c] = "failed"]
    \* If client was locking files, release them
    /\ fileLock' = [f \in Files |->
        IF fileLock[f] = c THEN NULL ELSE fileLock[f]]
    /\ UNCHANGED <<pool, fileLang>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E l \in Languages, c \in ClientIds : AddClientToPool(l, c)
    \/ \E f \in Files, c \in ClientIds : AcquireClient(f, c)
    \/ \E f \in Files : ReleaseClient(f)
    \/ \E c \in ClientIds : ClientFails(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

(* Pool size never exceeds maximum *)
PoolSizeLimit ==
    \A l \in Languages : Cardinality(pool[l]) <= MaxPoolSize

(* Only in_use clients can hold file locks *)
OnlyInUseClientsLock ==
    \A f \in Files :
        fileLock[f] # NULL => clientState[fileLock[f]] = "in_use"

(* Available clients don't hold locks *)
AvailableNoLocks ==
    \A c \in ClientIds :
        clientState[c] = "available" =>
            \A f \in Files : fileLock[f] # c

(* Mutual exclusion: each file locked by at most one client *)
MutualExclusion ==
    \A f \in Files : Cardinality({c \in ClientIds : fileLock[f] = c}) <= 1

(* Client language match: locking client must be in correct pool *)
ClientLanguageMatch ==
    \A f \in Files :
        fileLock[f] # NULL => fileLock[f] \in pool[fileLang[f]]

-----------------------------------------------------------------------------
(* Combined Invariant *)

Invariant ==
    /\ TypeOK
    /\ PoolSizeLimit
    /\ OnlyInUseClientsLock
    /\ AvailableNoLocks
    /\ MutualExclusion
    /\ ClientLanguageMatch

=============================================================================
