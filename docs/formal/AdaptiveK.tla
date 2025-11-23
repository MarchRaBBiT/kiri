---- MODULE AdaptiveK ----
EXTENDS Naturals, Sequences

CONSTANTS
  CATEGORIES,
  ALLOWED_SET,
  K_MIN,
  K_MAX,
  K_BUGFIX,
  K_INTEGRATION,
  K_TESTFAIL,
  K_PERFORMANCE,
  K_DEFAULT

(*************************************************************************)
(* Adaptive K mapping for search queries                                  *)
(*************************************************************************)
AdaptiveK(cat) ==
  IF cat = "bugfix" THEN K_BUGFIX
  ELSE IF cat = "integration" THEN K_INTEGRATION
  ELSE IF cat = "testfail" THEN K_TESTFAIL
  ELSE IF cat = "performance" THEN K_PERFORMANCE
  ELSE K_DEFAULT

VARIABLES queryCat, k

Init ==
  /\ queryCat \in CATEGORIES
  /\ k = AdaptiveK(queryCat)

Next ==
  \E newCat \in CATEGORIES:
    /\ queryCat' = newCat
    /\ k' = AdaptiveK(newCat)

InvAllowedSet == k \in ALLOWED_SET

InvRange == K_MIN <= k /\ k <= K_MAX

InvBugfixPrecision == (queryCat = "bugfix") => k = K_BUGFIX

InvIntegrationPrecision == (queryCat = "integration") => k = K_INTEGRATION

InvTestfailRecall == (queryCat = "testfail") => k = K_TESTFAIL

InvPerformanceRecall == (queryCat = "performance") => k = K_PERFORMANCE

InvGenericBalance == (queryCat \notin {"bugfix", "integration", "testfail", "performance"}) => k = K_DEFAULT

Spec == Init /\ [][Next]_<<queryCat, k>>

THEOREM InvAllowedSetInvariant == Spec => []InvAllowedSet
THEOREM InvRangeInvariant == Spec => []InvRange
THEOREM InvBugfixPrecisionInvariant == Spec => []InvBugfixPrecision
THEOREM InvIntegrationPrecisionInvariant == Spec => []InvIntegrationPrecision
THEOREM InvTestfailRecallInvariant == Spec => []InvTestfailRecall
THEOREM InvPerformanceRecallInvariant == Spec => []InvPerformanceRecall
THEOREM InvGenericBalanceInvariant == Spec => []InvGenericBalance

====
