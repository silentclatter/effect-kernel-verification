------------------------- MODULE EffectKernel_TLA_R2 -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Subjects,
    RootGrant,
    ChildGrants,
    EffectIDs,
    Epochs,
    MaxBudget,
    MaxPolicyVer,
    MaxGrantVer,
    MetaIDs,
    Guarantees,
    a1, a2

VARIABLES
    ke_epoch,
    ke_policy,
    grants,
    ledger,
    omega,
    meta_consumed

vars == <<ke_epoch, ke_policy, grants, ledger, omega, meta_consumed>>

Grants == {RootGrant} \cup ChildGrants
EffectKeys == Epochs \X EffectIDs
AdapterIDs == {a1, a2}

PermSubsumes(p1, p2) == p1 >= p2

Adapters == [ad \in AdapterIDs |->
    IF ad = a1
    THEN [
        guarantees  |-> {"AtomicFreshness", "AuthCostAccounting", "AtMostOnce"},
        assumptions |-> TRUE
    ]
    ELSE [
        guarantees  |-> {"AtMostOnce"},
        assumptions |-> TRUE
    ]
]

Operations == {
    [perm |-> 5, target |-> a1, cost |-> 2, req |-> {"AtomicFreshness"}],
    [perm |-> 8, target |-> a2, cost |-> 3, req |-> {"AtMostOnce"}]
}

RECURSIVE Ancestors(_)
Ancestors(g) ==
    IF g = RootGrant THEN {}
    ELSE IF grants[g].parent = RootGrant THEN {RootGrant}
    ELSE {grants[g].parent} \cup Ancestors(grants[g].parent)

RECURSIVE EffectivePerm(_)
EffectivePerm(g) ==
    IF g = RootGrant THEN grants[g].perm
    ELSE IF grants[g].parent = g THEN grants[g].perm
    ELSE
        LET parentPerm == EffectivePerm(grants[g].parent)
            myPerm == grants[g].perm
        IN IF parentPerm < myPerm THEN parentPerm ELSE myPerm

RECURSIVE EffectiveActive(_)
EffectiveActive(g) ==
    /\ grants[g].status = "ACTIVE"
    /\ grants[g].time_valid = TRUE
    /\ (g # RootGrant => EffectiveActive(grants[g].parent))

RECURSIVE SumBudget(_)
SumBudget(S) ==
    IF S = {} THEN 0
    ELSE LET g == CHOOSE x \in S : TRUE
         IN (grants[g].budget_avail + grants[g].budget_resv + grants[g].budget_consumed)
            + SumBudget(S \ {g})

EmptyOmega == [
    status        |-> "NONE",
    physical      |-> "NONE",
    physical_cost |-> 0,
    reported_cost |-> 0
]

EmptyAuthSnapshot == [
    active      |-> FALSE,
    eff_perm    |-> 0,
    policy_ver  |-> 0,
    grant_ver   |-> 0,
    adapter_ok  |-> FALSE
]

Init ==
    /\ ke_epoch = 1
    /\ ke_policy = [conforms_C0 |-> TRUE, version |-> 1]
    /\ grants = [g \in Grants |->
         IF g = RootGrant
         THEN [status          |-> "ACTIVE",
               parent          |-> g,
               subject         |-> CHOOSE s \in Subjects : TRUE,
               perm            |-> 10,
               budget_avail    |-> MaxBudget,
               budget_resv     |-> 0,
               budget_consumed |-> 0,
               version         |-> 0,
               time_valid      |-> TRUE,
               delegable       |-> TRUE]
         ELSE [status          |-> "UNINIT",
               parent          |-> RootGrant,
               subject         |-> CHOOSE s \in Subjects : TRUE,
               perm            |-> 0,
               budget_avail    |-> 0,
               budget_resv     |-> 0,
               budget_consumed |-> 0,
               version         |-> 0,
               time_valid      |-> TRUE,
               delegable       |-> FALSE]]
    /\ ledger = [k \in EffectKeys |-> [
         state      |-> "UNSEEN",
         op         |-> [perm |-> 0, target |-> a1, cost |-> 0, req |-> {}],
         grant      |-> RootGrant,
         policy_ver |-> 0,
         grant_ver  |-> 0,
         resv       |-> 0,
         adapter    |-> a1,
         lin_pt     |-> FALSE,
         lin_auth   |-> EmptyAuthSnapshot,
         expired    |-> FALSE,
         visited    |-> {"UNSEEN"}
       ]]
    /\ omega = [k \in EffectKeys |-> EmptyOmega]
    /\ meta_consumed = {}

Prepare(subj, id, g, op, b_req) ==
    LET k == <<ke_epoch, id>> IN
    /\ ledger[k].state = "UNSEEN"
    /\ EffectiveActive(g)
    /\ grants[g].subject = subj
    /\ PermSubsumes(EffectivePerm(g), op.perm)
    /\ grants[g].budget_avail >= b_req
    /\ b_req >= op.cost
    /\ op.req \subseteq Adapters[op.target].guarantees
    /\ Adapters[op.target].assumptions = TRUE
    /\ grants' = [grants EXCEPT ![g].budget_avail = @ - b_req,
                                ![g].budget_resv  = @ + b_req]
    /\ ledger' = [ledger EXCEPT ![k] = [
         state      |-> "RESERVED",
         op         |-> op,
         grant      |-> g,
         policy_ver |-> ke_policy.version,
         grant_ver  |-> grants[g].version,
         resv       |-> b_req,
         adapter    |-> op.target,
         lin_pt     |-> FALSE,
         lin_auth   |-> EmptyAuthSnapshot,
         expired    |-> FALSE,
         visited    |-> {"UNSEEN", "RESERVED"}
       ]]
    /\ UNCHANGED <<ke_epoch, ke_policy, omega, meta_consumed>>

CommitStart(id) ==
    LET k == <<ke_epoch, id>>
        g == ledger[k].grant
        ad == ledger[k].adapter IN
    /\ ledger[k].state = "RESERVED"
    /\ ~ledger[k].expired
    /\ ke_policy.version = ledger[k].policy_ver
    /\ grants[g].version = ledger[k].grant_ver
    /\ EffectiveActive(g)
    /\ PermSubsumes(EffectivePerm(g), ledger[k].op.perm)
    /\ Adapters[ad].assumptions = TRUE
    /\ ledger' = [ledger EXCEPT
         ![k].state    = "DISPATCHING",
         ![k].lin_pt   = TRUE,
         ![k].lin_auth = [
             active     |-> EffectiveActive(g),
             eff_perm   |-> EffectivePerm(g),
             policy_ver |-> ke_policy.version,
             grant_ver  |-> grants[g].version,
             adapter_ok |-> Adapters[ad].assumptions
         ],
         ![k].visited  = @ \cup {"DISPATCHING"}
       ]
    /\ omega' = [omega EXCEPT ![k] = [
         status        |-> "PENDING",
         physical      |-> "NONE",
         physical_cost |-> 0,
         reported_cost |-> 0
       ]]
    /\ UNCHANGED <<ke_epoch, ke_policy, grants, meta_consumed>>

ExpireReservation(epoch, id) ==
    LET k == <<epoch, id>> IN
    /\ ledger[k].state = "RESERVED"
    /\ ~ledger[k].expired
    /\ ledger' = [ledger EXCEPT ![k].expired = TRUE]
    /\ UNCHANGED <<ke_epoch, ke_policy, grants, omega, meta_consumed>>

ExpireGrant(g) ==
    /\ grants[g].status = "ACTIVE"
    /\ grants[g].time_valid = TRUE
    /\ grants' = [grants EXCEPT ![g].time_valid = FALSE]
    /\ UNCHANGED <<ke_epoch, ke_policy, ledger, omega, meta_consumed>>

EnvEffectOccurred(epoch, id, p_cost, r_cost) ==
    LET k == <<epoch, id>>
        ad == ledger[k].adapter
        has_auth_acc == "AuthCostAccounting" \in Adapters[ad].guarantees IN
    /\ omega[k].status = "PENDING"
    /\ p_cost <= ledger[k].resv
    /\ IF has_auth_acc
       THEN r_cost = p_cost
       ELSE r_cost \in 0..p_cost
    /\ omega' = [omega EXCEPT ![k] = [
         status        |-> "OCCURRED",
         physical      |-> "OCCURRED",
         physical_cost |-> p_cost,
         reported_cost |-> r_cost
       ]]
    /\ UNCHANGED <<ke_epoch, ke_policy, grants, ledger, meta_consumed>>

EnvNoEffect(epoch, id) ==
    LET k == <<epoch, id>> IN
    /\ omega[k].status = "PENDING"
    /\ omega' = [omega EXCEPT ![k] = [
         status        |-> "NOEFFECT",
         physical      |-> "NOEFFECT",
         physical_cost |-> 0,
         reported_cost |-> 0
       ]]
    /\ UNCHANGED <<ke_epoch, ke_policy, grants, ledger, meta_consumed>>

EnvAmbiguous(epoch, id, phys_occurred, p_cost) ==
    LET k == <<epoch, id>> IN
    /\ omega[k].status = "PENDING"
    /\ IF phys_occurred
       THEN /\ p_cost <= ledger[k].resv
            /\ omega' = [omega EXCEPT ![k] = [
                 status        |-> "AMBIGUOUS",
                 physical      |-> "OCCURRED",
                 physical_cost |-> p_cost,
                 reported_cost |-> 0
               ]]
       ELSE /\ omega' = [omega EXCEPT ![k] = [
                 status        |-> "AMBIGUOUS",
                 physical      |-> "NOEFFECT",
                 physical_cost |-> 0,
                 reported_cost |-> 0
               ]]
    /\ UNCHANGED <<ke_epoch, ke_policy, grants, ledger, meta_consumed>>

CommitSuccess(epoch, id) ==
    LET k == <<epoch, id>>
        g == ledger[k].grant
        resv == ledger[k].resv
        r_cost == omega[k].reported_cost
        has_auth_acc == "AuthCostAccounting" \in Adapters[ledger[k].adapter].guarantees
        refund == IF has_auth_acc THEN resv - r_cost ELSE 0
        charge == resv - refund IN
    /\ ledger[k].state = "DISPATCHING"
    /\ omega[k].status = "OCCURRED"
    /\ grants' = [grants EXCEPT ![g].budget_resv     = @ - resv,
                                ![g].budget_consumed = @ + charge,
                                ![g].budget_avail    = @ + refund]
    /\ ledger' = [ledger EXCEPT ![k].state   = "COMMITTED",
                                ![k].visited = @ \cup {"COMMITTED"}]
    /\ omega' = [omega EXCEPT ![k] = EmptyOmega]
    /\ UNCHANGED <<ke_epoch, ke_policy, meta_consumed>>

CommitAbort(epoch, id) ==
    LET k == <<epoch, id>>
        g == ledger[k].grant
        resv == ledger[k].resv IN
    /\ ledger[k].state = "DISPATCHING"
    /\ omega[k].status = "NOEFFECT"
    /\ grants' = [grants EXCEPT ![g].budget_resv  = @ - resv,
                                ![g].budget_avail = @ + resv]
    /\ ledger' = [ledger EXCEPT ![k].state   = "ABORTED",
                                ![k].visited = @ \cup {"ABORTED"}]
    /\ omega' = [omega EXCEPT ![k] = EmptyOmega]
    /\ UNCHANGED <<ke_epoch, ke_policy, meta_consumed>>

TimeoutUnknown(epoch, id) ==
    LET k == <<epoch, id>>
        g == ledger[k].grant
        resv == ledger[k].resv IN
    /\ ledger[k].state = "DISPATCHING"
    /\ omega[k].status = "AMBIGUOUS"
    /\ grants' = [grants EXCEPT ![g].budget_resv     = @ - resv,
                                ![g].budget_consumed = @ + resv]
    /\ ledger' = [ledger EXCEPT ![k].state   = "UNKNOWN",
                                ![k].visited = @ \cup {"UNKNOWN"}]
    /\ omega' = [omega EXCEPT ![k] = EmptyOmega]
    /\ UNCHANGED <<ke_epoch, ke_policy, meta_consumed>>

CrashQuarantine(epoch, id) ==
    LET k == <<epoch, id>>
        g == ledger[k].grant
        resv == ledger[k].resv IN
    /\ ledger[k].state = "DISPATCHING"
    /\ omega[k].status = "PENDING"
    /\ grants' = [grants EXCEPT ![g].budget_resv     = @ - resv,
                                ![g].budget_consumed = @ + resv]
    /\ ledger' = [ledger EXCEPT ![k].state   = "UNKNOWN",
                                ![k].visited = @ \cup {"UNKNOWN"}]
    /\ omega' = [omega EXCEPT ![k] = EmptyOmega]
    /\ UNCHANGED <<ke_epoch, ke_policy, meta_consumed>>

TimeoutAbort(epoch, id) ==
    LET k == <<epoch, id>>
        g == ledger[k].grant
        resv == ledger[k].resv IN
    /\ ledger[k].state = "RESERVED"
    /\ ledger[k].expired = TRUE
    /\ grants' = [grants EXCEPT ![g].budget_resv  = @ - resv,
                                ![g].budget_avail = @ + resv]
    /\ ledger' = [ledger EXCEPT ![k].state   = "ABORTED",
                                ![k].visited = @ \cup {"ABORTED"}]
    /\ UNCHANGED <<ke_epoch, ke_policy, omega, meta_consumed>>

Delegate(subj_caller, p_grant, c_grant, p_perm, b_alloc, c_subj, c_del) ==
    /\ EffectiveActive(p_grant)
    /\ grants[p_grant].subject = subj_caller
    /\ grants[p_grant].delegable = TRUE
    /\ grants[c_grant].status = "UNINIT"
    /\ PermSubsumes(EffectivePerm(p_grant), p_perm)
    /\ p_perm >= 1
    /\ grants[p_grant].budget_avail >= b_alloc
    /\ grants' = [grants EXCEPT
         ![p_grant].budget_avail = @ - b_alloc,
         ![c_grant] = [status          |-> "ACTIVE",
                       parent          |-> p_grant,
                       subject         |-> c_subj,
                       perm            |-> p_perm,
                       budget_avail    |-> b_alloc,
                       budget_resv     |-> 0,
                       budget_consumed |-> 0,
                       version         |-> 0,
                       time_valid      |-> TRUE,
                       delegable       |-> c_del]]
    /\ UNCHANGED <<ke_epoch, ke_policy, ledger, omega, meta_consumed>>

Revoke(subj_caller, caller_grant, target_grant) ==
    /\ grants[caller_grant].status = "ACTIVE"
    /\ grants[caller_grant].subject = subj_caller
    /\ (caller_grant \in Ancestors(target_grant) \/ caller_grant = target_grant)
    /\ grants[target_grant].status # "REVOKED"
    /\ grants[target_grant].version < MaxGrantVer
    /\ grants' = [grants EXCEPT
         ![target_grant].status  = "REVOKED",
         ![target_grant].version = @ + 1]
    /\ UNCHANGED <<ke_epoch, ke_policy, ledger, omega, meta_consumed>>

SelfAttenuate(subj_caller, g, narrowed_perm, forfeit_b) ==
    /\ grants[g].status = "ACTIVE"
    /\ grants[g].subject = subj_caller
    /\ grants[g].perm >= narrowed_perm
    /\ narrowed_perm >= 1
    /\ grants[g].budget_avail >= forfeit_b
    /\ (narrowed_perm < grants[g].perm \/ forfeit_b > 0)
    /\ grants[g].version < MaxGrantVer
    /\ grants' = [grants EXCEPT
         ![g].perm         = narrowed_perm,
         ![g].budget_avail = @ - forfeit_b,
         ![g].version      = @ + 1]
    /\ UNCHANGED <<ke_epoch, ke_policy, ledger, omega, meta_consumed>>

UpdatePolicyExpand(meta_id) ==
    /\ <<ke_epoch, meta_id>> \notin meta_consumed
    /\ ke_policy.version < MaxPolicyVer
    /\ meta_consumed' = meta_consumed \cup {<<ke_epoch, meta_id>>}
    /\ ke_policy' = [conforms_C0 |-> TRUE, version |-> ke_policy.version + 1]
    /\ UNCHANGED <<ke_epoch, grants, ledger, omega>>

ReprovisionTCB ==
    /\ ke_epoch < 2
    /\ ke_epoch' = ke_epoch + 1
    /\ ke_policy' = [conforms_C0 |-> TRUE, version |-> 1]
    /\ UNCHANGED <<grants, ledger, omega, meta_consumed>>

TypeOK ==
    /\ ke_epoch \in Epochs
    /\ ke_policy.conforms_C0 \in BOOLEAN
    /\ ke_policy.version \in 1..MaxPolicyVer
    /\ meta_consumed \subseteq (Epochs \X MetaIDs)
    /\ \A g \in Grants :
        /\ grants[g].status \in {"ACTIVE", "REVOKED", "UNINIT"}
        /\ grants[g].parent \in Grants
        /\ grants[g].subject \in Subjects
        /\ grants[g].perm \in 0..10
        /\ grants[g].budget_avail \in 0..MaxBudget
        /\ grants[g].budget_resv \in 0..MaxBudget
        /\ grants[g].budget_consumed \in 0..MaxBudget
        /\ grants[g].version \in 0..MaxGrantVer
        /\ grants[g].time_valid \in BOOLEAN
        /\ grants[g].delegable \in BOOLEAN
    /\ \A k \in EffectKeys :
        /\ ledger[k].state \in {"UNSEEN", "RESERVED", "DISPATCHING", "COMMITTED", "ABORTED", "UNKNOWN"}
        /\ ledger[k].grant \in Grants
        /\ ledger[k].resv \in 0..MaxBudget
        /\ ledger[k].policy_ver \in 0..MaxPolicyVer
        /\ ledger[k].grant_ver \in 0..MaxGrantVer
        /\ ledger[k].adapter \in AdapterIDs
        /\ ledger[k].lin_pt \in BOOLEAN
        /\ ledger[k].expired \in BOOLEAN
        /\ ledger[k].visited \subseteq {"UNSEEN", "RESERVED", "DISPATCHING", "COMMITTED", "ABORTED", "UNKNOWN"}
        /\ omega[k].status \in {"NONE", "PENDING", "OCCURRED", "NOEFFECT", "AMBIGUOUS"}
        /\ omega[k].physical \in {"NONE", "OCCURRED", "NOEFFECT"}
        /\ omega[k].physical_cost \in 0..MaxBudget
        /\ omega[k].reported_cost \in 0..MaxBudget

I1_ConstitutionalSubsumption == ke_policy.conforms_C0 = TRUE

I2_MonotoneLineageAuthority ==
    \A g \in Grants :
        (grants[g].status = "ACTIVE" /\ g # RootGrant) =>
            EffectivePerm(g) <= EffectivePerm(grants[g].parent)

I3_DiscreteBudgetNonMultiplication ==
    SumBudget(Grants) <= MaxBudget

I4_MonotonicLifecycleProgression ==
    \A k \in EffectKeys :
        /\ ledger[k].state \in ledger[k].visited
        /\ (ledger[k].state = "UNSEEN" => ledger[k].visited = {"UNSEEN"})
        /\ (ledger[k].state = "RESERVED" => ledger[k].visited = {"UNSEEN", "RESERVED"})
        /\ (ledger[k].state = "DISPATCHING" => ledger[k].visited = {"UNSEEN", "RESERVED", "DISPATCHING"})
        /\ (ledger[k].state = "COMMITTED" => ledger[k].visited = {"UNSEEN", "RESERVED", "DISPATCHING", "COMMITTED"})
        /\ (ledger[k].state = "UNKNOWN" => ledger[k].visited = {"UNSEEN", "RESERVED", "DISPATCHING", "UNKNOWN"})
        /\ (ledger[k].state = "ABORTED" =>
                \/ ledger[k].visited = {"UNSEEN", "RESERVED", "ABORTED"}
                \/ ledger[k].visited = {"UNSEEN", "RESERVED", "DISPATCHING", "ABORTED"})

I5_LinearizedAdmissionSoundness ==
    \A k \in EffectKeys :
        (ledger[k].lin_pt = TRUE) =>
            /\ ledger[k].lin_auth.active = TRUE
            /\ PermSubsumes(ledger[k].lin_auth.eff_perm, ledger[k].op.perm)
            /\ ledger[k].lin_auth.policy_ver = ledger[k].policy_ver
            /\ ledger[k].lin_auth.grant_ver = ledger[k].grant_ver
            /\ ledger[k].lin_auth.adapter_ok = TRUE

I6_PhysicalFidelityAndBoundedness ==
    \A k \in EffectKeys :
        (omega[k].physical = "OCCURRED") =>
            omega[k].physical_cost <= ledger[k].resv

I7_TargetContractCompliance ==
    \A k \in EffectKeys :
        (ledger[k].state \in {"DISPATCHING", "COMMITTED", "UNKNOWN"}) =>
            /\ ledger[k].op.req \subseteq Adapters[ledger[k].adapter].guarantees
            /\ Adapters[ledger[k].adapter].assumptions = TRUE

SpecInv ==
    /\ TypeOK
    /\ I1_ConstitutionalSubsumption
    /\ I2_MonotoneLineageAuthority
    /\ I3_DiscreteBudgetNonMultiplication
    /\ I4_MonotonicLifecycleProgression
    /\ I5_LinearizedAdmissionSoundness
    /\ I6_PhysicalFidelityAndBoundedness
    /\ I7_TargetContractCompliance

SymmetryPermutations == Permutations(EffectIDs)

Next ==
    \/ \E s \in Subjects, id \in EffectIDs, g \in Grants, op \in Operations, b \in 1..MaxBudget :
        Prepare(s, id, g, op, b)
    \/ \E id \in EffectIDs : CommitStart(id)
    \/ \E e \in Epochs, id \in EffectIDs : ExpireReservation(e, id)
    \/ \E g \in Grants : ExpireGrant(g)
    \/ \E e \in Epochs, id \in EffectIDs, p \in 0..MaxBudget, r \in 0..MaxBudget :
        EnvEffectOccurred(e, id, p, r)
    \/ \E e \in Epochs, id \in EffectIDs : EnvNoEffect(e, id)
    \/ \E e \in Epochs, id \in EffectIDs, occ \in BOOLEAN, p \in 0..MaxBudget :
        EnvAmbiguous(e, id, occ, p)
    \/ \E e \in Epochs, id \in EffectIDs : CommitSuccess(e, id)
    \/ \E e \in Epochs, id \in EffectIDs : CommitAbort(e, id)
    \/ \E e \in Epochs, id \in EffectIDs : TimeoutUnknown(e, id)
    \/ \E e \in Epochs, id \in EffectIDs : CrashQuarantine(e, id)
    \/ \E e \in Epochs, id \in EffectIDs : TimeoutAbort(e, id)
    \/ \E s \in Subjects, p \in Grants, c \in ChildGrants, perm \in 1..10, b \in 0..MaxBudget, cs \in Subjects, cd \in BOOLEAN :
        Delegate(s, p, c, perm, b, cs, cd)
    \/ \E s \in Subjects, cg \in Grants, tg \in Grants : Revoke(s, cg, tg)
    \/ \E s \in Subjects, g \in Grants, perm \in 1..10, b \in 0..MaxBudget : SelfAttenuate(s, g, perm, b)
    \/ \E m \in MetaIDs : UpdatePolicyExpand(m)
    \/ ReprovisionTCB

Spec == Init /\ [][Next]_vars
=============================================================================
