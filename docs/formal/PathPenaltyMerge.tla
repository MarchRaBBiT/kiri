---- MODULE PathPenaltyMerge ----
EXTENDS Naturals, Integers, Sequences, PathPenaltyEncoding

(*
  This module models how Issue #106 requires path-specific scoring multipliers to be
  merged from three layers (boost profile defaults, environment overrides, repo-level
  YAML config) and then applied to candidate paths. Multipliers are represented as
  integer percentages (e.g., 30 ≈ 0.3x, 150 ≈ 1.5x) to keep the state space finite.
*)

DefaultMultiplier == 100

Prefixes == {
  "external/",
  "external/assay-kit/",
  "src/",
  "src/server/"
}

PrefixOrder == << "external/assay-kit/", "external/", "src/server/", "src/" >>

Paths == {
  "external/assay-kit/sql/migration.ts",
  "external/README.md",
  "src/server/handlers.ts",
  "src/indexer/pipeline.ts"
}

CONSTANTS MaxSeqLenYaml, MaxSeqLenEnv, MaxSeqLenProfile

ASSUME BoundedSequenceLengths ==
  /\ MaxSeqLenYaml \in Nat
  /\ MaxSeqLenEnv \in Nat
  /\ MaxSeqLenProfile \in Nat
(*
  Production settings permit arbitrary-length configurations; these bounds exist solely
  to keep the TLC model finite. Increase them per cfg when running deeper checks.
*)

MultiplierValues == {20, 30, 70, 80, 100, 150, 180}

Entry(p, m) == [prefix |-> p, multiplier |-> m]

EntryPool == {
  Entry("external/", 30),
  Entry("external/", 70),
  Entry("external/assay-kit/", 20),
  Entry("src/", 100),
  Entry("src/", 150),
  Entry("src/server/", 80),
  Entry("src/server/", 180)
}

(*
  OSNormalize (defined in PathPenaltyEncoding) conceptually converts Windows-style "\"
  separators and relative segments to forward-slash, absolute prefixes. Implementation
  code performs the actual normalization, so in this model we simply assume all prefixes
  already satisfy OSNormalize(prefix) = prefix.
*)

ASSUME PrefixesAreNormalized ==
  \A entry \in EntryPool : OSNormalize(entry.prefix) = entry.prefix

SeqPrefixes(seq) ==
  { (seq[i]).prefix : i \in 1 .. Len(seq) }

AppendEntry(seq, entry) == seq \o <<entry>>

(*
  Duplicate prefixes are allowed in the sequences; LastValue/WinningMultiplier model
  the "last definition wins" policy used by the implementation.
*)
RECURSIVE Seqs(_)
Seqs(n) ==
  IF n = 0
    THEN { <<>> }
    ELSE
      { AppendEntry(seq, entry) : seq \in Seqs(n - 1), entry \in EntryPool }

SequenceOptionsYaml == UNION { Seqs(i) : i \in 0 .. MaxSeqLenYaml }
SequenceOptionsEnv == UNION { Seqs(i) : i \in 0 .. MaxSeqLenEnv }
SequenceOptionsProfile == UNION { Seqs(i) : i \in 0 .. MaxSeqLenProfile }

VARIABLES yamlSeq, envSeq, profileSeq

Init ==
  /\ yamlSeq \in SequenceOptionsYaml
  /\ envSeq \in SequenceOptionsEnv
  /\ profileSeq \in SequenceOptionsProfile

Next == UNCHANGED <<yamlSeq, envSeq, profileSeq>>

Spec == Init /\ [][Next]_<<yamlSeq, envSeq, profileSeq>>

NoValue == -1

RECURSIVE ApplyEntries(_, _)
ApplyEntries(map, seq) ==
  IF Len(seq) = 0
    THEN map
    ELSE
      LET entry == Head(seq) IN
        ApplyEntries([map EXCEPT ![entry.prefix] = entry.multiplier], Tail(seq))

DefaultMap == [p \in Prefixes |-> DefaultMultiplier]

Merge(yaml, env, profile) ==
  LET afterProfile == ApplyEntries(DefaultMap, profile)
      afterEnv == ApplyEntries(afterProfile, env)
      afterYaml == ApplyEntries(afterEnv, yaml)
  IN afterYaml

RECURSIVE LastValue(_, _)
LastValue(seq, prefix) ==
  IF Len(seq) = 0
    THEN NoValue
    ELSE
      LET tailVal == LastValue(Tail(seq), prefix)
          headEntry == Head(seq)
      IN
        IF tailVal # NoValue
          THEN tailVal
          ELSE IF headEntry.prefix = prefix
            THEN headEntry.multiplier
            ELSE NoValue

WinningMultiplier(prefix, yaml, env, profile) ==
  LET yamlVal == LastValue(yaml, prefix)
      envVal == LastValue(env, prefix)
      profileVal == LastValue(profile, prefix)
  IN
    IF yamlVal # NoValue
      THEN yamlVal
      ELSE IF envVal # NoValue
        THEN envVal
        ELSE IF profileVal # NoValue
          THEN profileVal
          ELSE DefaultMultiplier

IsPrefix(prefix, path) ==
  /\ Len(prefix) <= Len(path)
  /\ prefix = SubSeq(path, 1, Len(prefix))

Matches(path) == {p \in Prefixes : IsPrefix(p, path)}

BestMultiplier(map, path) ==
  LET matches == Matches(path)
  IN
    IF matches = {}
      THEN DefaultMultiplier
      ELSE
        LET best == CHOOSE q \in matches :
                    \A r \in matches : Len(q) >= Len(r)
        IN map[best]

ReferenceMultiplier(path, yaml, env, profile) ==
  LET matches == Matches(path)
  IN
    IF matches = {}
      THEN DefaultMultiplier
      ELSE
        LET best == CHOOSE q \in matches :
                    \A r \in matches : Len(q) >= Len(r)
        IN WinningMultiplier(best, yaml, env, profile)

BuildSortedList(map) ==
  (*
    config-loader sorts pathMultipliers by descending prefix length before handing
    them to the scoring loop. PrefixOrder models the resulting order so the spec
    matches src/server/config-loader.ts and src/server/handlers.ts (getPathMultiplier).
  *)
  [i \in 1..Len(PrefixOrder) |->
    [prefix |-> PrefixOrder[i], multiplier |-> map[PrefixOrder[i]]]]

RECURSIVE FirstMatchMultiplier(_, _)
FirstMatchMultiplier(seq, path) ==
  IF Len(seq) = 0
    THEN DefaultMultiplier
    ELSE
      LET entry == Head(seq)
      IN
        IF IsPrefix(entry.prefix, path)
          THEN entry.multiplier
          ELSE FirstMatchMultiplier(Tail(seq), path)

SimulationMultiplier(path, map) ==
  FirstMatchMultiplier(BuildSortedList(map), path)

MergePrecedenceInvariant ==
  LET merged == Merge(yamlSeq, envSeq, profileSeq)
  IN
    \A p \in Prefixes :
      merged[p] = WinningMultiplier(p, yamlSeq, envSeq, profileSeq)

LongestPrefixInvariant ==
  LET merged == Merge(yamlSeq, envSeq, profileSeq)
  IN
    \A path \in Paths :
      BestMultiplier(merged, path) = ReferenceMultiplier(path, yamlSeq, envSeq, profileSeq)

ScanMatchesInvariant ==
  LET merged == Merge(yamlSeq, envSeq, profileSeq)
  IN
    \A path \in Paths :
      BestMultiplier(merged, path) = SimulationMultiplier(path, merged)

EncodeDecodeInvariant ==
  LET combined ==
    SeqPrefixes(yamlSeq) \cup SeqPrefixes(envSeq) \cup SeqPrefixes(profileSeq)
  IN
    \A prefix \in combined : Decode(Encode(prefix)) = prefix

(*
  Trivial liveness-style property: once the configuration is chosen, it stays
  consistent forever (context_bundle applies static multipliers per request).
*)
EventuallyConsistent ==
  <>[](
    MergePrecedenceInvariant /\ LongestPrefixInvariant /\ ScanMatchesInvariant /\ EncodeDecodeInvariant
  )

====
