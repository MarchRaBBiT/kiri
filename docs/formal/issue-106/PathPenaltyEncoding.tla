---- MODULE PathPenaltyEncoding ----
EXTENDS Naturals, Sequences

(*
  Utility operators for encoding/decoding path prefixes and handling
  platform-specific normalization. Separated from PathPenaltyMerge so the
  encoding logic can be tested or replaced independently (e.g., Alloy models).
*)

Slash == "/"
Underscore == "_"

TailStr(str) ==
  IF Len(str) <= 1
    THEN ""
    ELSE SubSeq(str, 2, Len(str))

DropChars(str, n) ==
  IF Len(str) <= n
    THEN ""
    ELSE SubSeq(str, n + 1, Len(str))

RECURSIVE EncodeStr(_)
EncodeStr(str) ==
  IF Len(str) = 0
    THEN ""
    ELSE
      LET ch == SubSeq(str, 1, 1)
      IN
        IF ch = Slash
          THEN "__" \o EncodeStr(TailStr(str))
          ELSE ch \o EncodeStr(TailStr(str))

Encode(prefix) == EncodeStr(prefix)

RECURSIVE DecodeStr(_)
DecodeStr(str) ==
  IF Len(str) = 0
    THEN ""
    ELSE
      LET first == SubSeq(str, 1, 1)
      IN
        IF first = Underscore /\ Len(str) >= 2 /\ SubSeq(str, 2, 2) = Underscore
          THEN Slash \o DecodeStr(DropChars(str, 2))
          ELSE first \o DecodeStr(TailStr(str))

Decode(encoded) == DecodeStr(encoded)

(*
  Placeholder for platform normalization. Production code resolves ".", "..",
  Windows drive letters, and "\" separators. Here we treat prefixes as already
  normalized to keep the state space finite while still documenting the contract.
*)
OSNormalize(prefix) == prefix

====
