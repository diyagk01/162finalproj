### Task 5: Sensitivity analysis - parameterized version of Task 4 ###
# Identical model to task4.mod except p and dmul (demand multiplier)
# are parameters that can be changed via `let` between solves.

set VENUES ordered;
set SPORTS;
set WEEKS  ordered;

param c     {VENUES};
param Cap   {VENUES};
param kappa {VENUES};
param a     {VENUES, SPORTS} binary;
param D     {SPORTS};
param R     {SPORTS};

param p;                       # profit per ticket ($) — set in run file
param dmul default 1.0;        # demand multiplier — set in run file
param F := 20;                 # bus-network fixed cost (thousand $)

# m must be set in the run file via `let` (after loading data and dmul).
# We declare it here without an assignment so it can be reassigned per scenario.
param m {VENUES, SPORTS};

set N2 := setof {i in VENUES, k in VENUES: ord(i) < ord(k)} (i,k);
set N3 := setof {i in VENUES, k in VENUES, l in VENUES:
                 ord(i) < ord(k) and ord(k) < ord(l)} (i,k,l);

var y {VENUES} binary;
var z {VENUES, SPORTS, WEEKS} binary;
var w {SPORTS, WEEKS} binary;

var b2 {N2} binary;
var b3 {N3} binary;
var u2  {N2, WEEKS} binary;
var u3F {N3, WEEKS} binary;
var u3A {N3, WEEKS} binary;
var u3B {N3, WEEKS} binary;
var u3C {N3, WEEKS} binary;
var rev2  {N2, WEEKS} >= 0;
var rev3F {N3, WEEKS} >= 0;
var rev3A {N3, WEEKS} >= 0;
var rev3B {N3, WEEKS} >= 0;
var rev3C {N3, WEEKS} >= 0;

minimize NetCost:
      sum {i in VENUES} c[i] * y[i]
    + F * (sum {(i,k)   in N2} b2[i,k]
         + sum {(i,k,l) in N3} b3[i,k,l])
    - p * sum {i in VENUES, j in SPORTS, t in WEEKS} m[i,j] * z[i,j,t]
    - p * sum {(i,k)   in N2, t in WEEKS} rev2[i,k,t]
    - p * sum {(i,k,l) in N3, t in WEEKS}
            (rev3F[i,k,l,t] + rev3A[i,k,l,t] + rev3B[i,k,l,t] + rev3C[i,k,l,t]);

# Scheduling
subject to OneWeekPerSport      {j in SPORTS}: sum {t in WEEKS} w[j,t] = 1;
subject to SessionsInChosenWeek {j in SPORTS, t in WEEKS}: sum {i in VENUES} z[i,j,t] = R[j] * w[j,t];
subject to VenueWeekCapacity    {i in VENUES, t in WEEKS}: sum {j in SPORTS} z[i,j,t] <= y[i];
subject to Eligibility          {i in VENUES, j in SPORTS, t in WEEKS}: z[i,j,t] <= a[i,j];
subject to WeekLimit            {i in VENUES, j in SPORTS, t in WEEKS: ord(t) > kappa[i]}: z[i,j,t] = 0;

# Bus networks
subject to OneNetworkPerVenue {v in VENUES}:
      sum {(i,k)   in N2: i = v or k = v}            b2[i,k]
    + sum {(i,k,l) in N3: i = v or k = v or l = v}   b3[i,k,l]
    <= 1;
subject to B2_open_i {(i,k)   in N2}:  b2[i,k]   <= y[i];
subject to B2_open_k {(i,k)   in N2}:  b2[i,k]   <= y[k];
subject to B3_open_i {(i,k,l) in N3}:  b3[i,k,l] <= y[i];
subject to B3_open_k {(i,k,l) in N3}:  b3[i,k,l] <= y[k];
subject to B3_open_l {(i,k,l) in N3}:  b3[i,k,l] <= y[l];

# Activations
subject to U2_b  {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= b2[i,k];
subject to U2_hi {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= sum {j in SPORTS} z[i,j,t];
subject to U2_hk {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= sum {j in SPORTS} z[k,j,t];

subject to U3F_b  {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= b3[i,k,l];
subject to U3F_hi {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3F_hk {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3F_hl {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];

subject to U3A_b  {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= b3[i,k,l];
subject to U3A_hi {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3A_hk {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3A_nl {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= 1 - sum {j in SPORTS} z[l,j,t];

subject to U3B_b  {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= b3[i,k,l];
subject to U3B_hi {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3B_hl {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];
subject to U3B_nk {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= 1 - sum {j in SPORTS} z[k,j,t];

subject to U3C_b  {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= b3[i,k,l];
subject to U3C_hk {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3C_hl {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];
subject to U3C_ni {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= 1 - sum {j in SPORTS} z[i,j,t];

subject to U3_OneMode {(i,k,l) in N3, t in WEEKS}:
    u3F[i,k,l,t] + u3A[i,k,l,t] + u3B[i,k,l,t] + u3C[i,k,l,t] <= b3[i,k,l];

# Revenue linking
subject to Rev2_spec {(i,k) in N2, t in WEEKS}:
    rev2[i,k,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t]);
subject to Rev2_cap  {(i,k) in N2, t in WEEKS}:
    rev2[i,k,t] <= 0.10 * (Cap[i] + Cap[k]) * u2[i,k,t];

subject to Rev3F_spec {(i,k,l) in N3, t in WEEKS}:
    rev3F[i,k,l,t] <= 0.14 * sum {j in SPORTS}
        (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3F_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3F[i,k,l,t] <= 0.14 * (Cap[i] + Cap[k] + Cap[l]) * u3F[i,k,l,t];

subject to Rev3A_spec {(i,k,l) in N3, t in WEEKS}:
    rev3A[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t]);
subject to Rev3A_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3A[i,k,l,t] <= 0.10 * (Cap[i] + Cap[k]) * u3A[i,k,l,t];

subject to Rev3B_spec {(i,k,l) in N3, t in WEEKS}:
    rev3B[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3B_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3B[i,k,l,t] <= 0.10 * (Cap[i] + Cap[l]) * u3B[i,k,l,t];

subject to Rev3C_spec {(i,k,l) in N3, t in WEEKS}:
    rev3C[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[k,j]*z[k,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3C_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3C[i,k,l,t] <= 0.10 * (Cap[k] + Cap[l]) * u3C[i,k,l,t];
