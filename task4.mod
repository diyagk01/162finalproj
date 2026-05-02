### Task 4: Multi-week scheduling, ticket revenue, and bus networks ###

set VENUES ordered;          # ordered so we can use ord() to enumerate networks
set SPORTS;
set WEEKS ordered;

# --- Parameters ---
param c     {VENUES};                  # fixed opening cost (thousand $)
param Cap   {VENUES};                  # seating capacity (thousands of seats)
param kappa {VENUES};                  # number of weeks venue is available
param a     {VENUES, SPORTS} binary;   # eligibility matrix
param D     {SPORTS};                  # demand per session (thousands of tickets)
param R     {SPORTS};                  # required sessions per sport
param p := 10;                         # profit per ticket ($); 10 * thousand tickets = thousand $
param F := 20;                         # fixed cost of a bus network (thousand $)

# Tickets sold per session of sport j held at venue i (thousands).
param m {i in VENUES, j in SPORTS} := min(D[j], Cap[i]);

# --- Network candidate sets (unordered combinations) ---
set N2 := {i in VENUES, k in VENUES: ord(i) < ord(k)};
set N3 := {i in VENUES, k in VENUES, l in VENUES:
           ord(i) < ord(k) and ord(k) < ord(l)};

# --- Decision variables (scheduling, same as Task 3) ---
var y {i in VENUES} binary;                            # 1 if venue i is opened
var z {i in VENUES, j in SPORTS, t in WEEKS} binary;   # 1 if sport j has a session at venue i in week t
var w {j in SPORTS, t in WEEKS} binary;                # 1 if sport j is scheduled in week t

# --- Bus-network decision variables ---
var b2 {N2} binary;                # 1 if 2-venue network is established
var b3 {N3} binary;                # 1 if 3-venue network is established

# Activation indicators (per network, per week)
var u2  {N2, WEEKS} binary;        # 2-venue net active (both venues hosting)
var u3F {N3, WEEKS} binary;        # 3-venue net: all 3 hosting (FULL)
var u3A {N3, WEEKS} binary;        # 3-venue net: only i,k hosting (l idle)
var u3B {N3, WEEKS} binary;        # 3-venue net: only i,l hosting (k idle)
var u3C {N3, WEEKS} binary;        # 3-venue net: only k,l hosting (i idle)

# Auxiliary "additional tickets" variables (thousands).
# These capture bilinear terms (binary activation x continuous spectator counts).
var rev2  {N2, WEEKS} >= 0;
var rev3F {N3, WEEKS} >= 0;
var rev3A {N3, WEEKS} >= 0;
var rev3B {N3, WEEKS} >= 0;
var rev3C {N3, WEEKS} >= 0;

# --- Objective: minimize venue cost + bus cost - all ticket revenue ---
minimize NetCost:
      sum {i in VENUES} c[i] * y[i]
    + F * (sum {(i,k)   in N2} b2[i,k]
         + sum {(i,k,l) in N3} b3[i,k,l])
    - p * sum {i in VENUES, j in SPORTS, t in WEEKS} m[i,j] * z[i,j,t]
    - p * sum {(i,k)   in N2, t in WEEKS} rev2[i,k,t]
    - p * sum {(i,k,l) in N3, t in WEEKS}
            (rev3F[i,k,l,t] + rev3A[i,k,l,t] + rev3B[i,k,l,t] + rev3C[i,k,l,t]);

# =====================================================================
# Scheduling constraints (identical to Task 3)
# =====================================================================
subject to OneWeekPerSport {j in SPORTS}:
    sum {t in WEEKS} w[j,t] = 1;

subject to SessionsInChosenWeek {j in SPORTS, t in WEEKS}:
    sum {i in VENUES} z[i,j,t] = R[j] * w[j,t];

subject to VenueWeekCapacity {i in VENUES, t in WEEKS}:
    sum {j in SPORTS} z[i,j,t] <= y[i];

subject to Eligibility {i in VENUES, j in SPORTS, t in WEEKS}:
    z[i,j,t] <= a[i,j];

subject to WeekLimit {i in VENUES, j in SPORTS, t in WEEKS: ord(t) > kappa[i]}:
    z[i,j,t] = 0;

# =====================================================================
# Bus-network structural constraints
# =====================================================================

# Each venue belongs to at most one bus network (2- or 3-venue).
subject to OneNetworkPerVenue {v in VENUES}:
      sum {(i,k)   in N2: i = v or k = v}             b2[i,k]
    + sum {(i,k,l) in N3: i = v or k = v or l = v}    b3[i,k,l]
    <= 1;

# A network can only be established between opened venues (tightening).
subject to B2_open_i {(i,k)   in N2}:  b2[i,k]   <= y[i];
subject to B2_open_k {(i,k)   in N2}:  b2[i,k]   <= y[k];
subject to B3_open_i {(i,k,l) in N3}:  b3[i,k,l] <= y[i];
subject to B3_open_k {(i,k,l) in N3}:  b3[i,k,l] <= y[k];
subject to B3_open_l {(i,k,l) in N3}:  b3[i,k,l] <= y[l];

# =====================================================================
# 2-venue activation: u2 = b2 AND (i hosts) AND (k hosts) in week t
# =====================================================================
subject to U2_b  {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= b2[i,k];
subject to U2_hi {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= sum {j in SPORTS} z[i,j,t];
subject to U2_hk {(i,k) in N2, t in WEEKS}: u2[i,k,t] <= sum {j in SPORTS} z[k,j,t];

# =====================================================================
# 3-venue activation: FULL (all three host)
# =====================================================================
subject to U3F_b  {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= b3[i,k,l];
subject to U3F_hi {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3F_hk {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3F_hl {(i,k,l) in N3, t in WEEKS}: u3F[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];

# 3-venue activation: PARTIAL A — only i,k host (l idle)
subject to U3A_b  {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= b3[i,k,l];
subject to U3A_hi {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3A_hk {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3A_nl {(i,k,l) in N3, t in WEEKS}: u3A[i,k,l,t] <= 1 - sum {j in SPORTS} z[l,j,t];

# 3-venue activation: PARTIAL B — only i,l host (k idle)
subject to U3B_b  {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= b3[i,k,l];
subject to U3B_hi {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= sum {j in SPORTS} z[i,j,t];
subject to U3B_hl {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];
subject to U3B_nk {(i,k,l) in N3, t in WEEKS}: u3B[i,k,l,t] <= 1 - sum {j in SPORTS} z[k,j,t];

# 3-venue activation: PARTIAL C — only k,l host (i idle)
subject to U3C_b  {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= b3[i,k,l];
subject to U3C_hk {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= sum {j in SPORTS} z[k,j,t];
subject to U3C_hl {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= sum {j in SPORTS} z[l,j,t];
subject to U3C_ni {(i,k,l) in N3, t in WEEKS}: u3C[i,k,l,t] <= 1 - sum {j in SPORTS} z[i,j,t];

# At most one mode of a given 3-venue network can be active in a week
# (already implied by the constraints above, but tightens the relaxation).
subject to U3_OneMode {(i,k,l) in N3, t in WEEKS}:
    u3F[i,k,l,t] + u3A[i,k,l,t] + u3B[i,k,l,t] + u3C[i,k,l,t] <= b3[i,k,l];

# =====================================================================
# Revenue linearization (rev_mode <= rate * spec_sum, and <= rate * cap_sum * u_mode)
# When the activation u is 0, the second bound forces rev = 0.
# When u = 1, the first bound is tight; the optimizer pushes rev up since it appears with a + sign in revenue.
# =====================================================================

# 2-venue: rate = 10%
subject to Rev2_spec {(i,k) in N2, t in WEEKS}:
    rev2[i,k,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t]);
subject to Rev2_cap  {(i,k) in N2, t in WEEKS}:
    rev2[i,k,t] <= 0.10 * (Cap[i] + Cap[k]) * u2[i,k,t];

# 3-venue FULL: rate = 14% (each venue contributes 7% to each of the other two)
subject to Rev3F_spec {(i,k,l) in N3, t in WEEKS}:
    rev3F[i,k,l,t] <= 0.14 * sum {j in SPORTS}
        (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3F_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3F[i,k,l,t] <= 0.14 * (Cap[i] + Cap[k] + Cap[l]) * u3F[i,k,l,t];

# 3-venue PARTIAL A (only i,k hosting): rate = 10% on i,k
subject to Rev3A_spec {(i,k,l) in N3, t in WEEKS}:
    rev3A[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[k,j]*z[k,j,t]);
subject to Rev3A_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3A[i,k,l,t] <= 0.10 * (Cap[i] + Cap[k]) * u3A[i,k,l,t];

# 3-venue PARTIAL B (only i,l hosting): rate = 10% on i,l
subject to Rev3B_spec {(i,k,l) in N3, t in WEEKS}:
    rev3B[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[i,j]*z[i,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3B_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3B[i,k,l,t] <= 0.10 * (Cap[i] + Cap[l]) * u3B[i,k,l,t];

# 3-venue PARTIAL C (only k,l hosting): rate = 10% on k,l
subject to Rev3C_spec {(i,k,l) in N3, t in WEEKS}:
    rev3C[i,k,l,t] <= 0.10 * sum {j in SPORTS} (m[k,j]*z[k,j,t] + m[l,j]*z[l,j,t]);
subject to Rev3C_cap  {(i,k,l) in N3, t in WEEKS}:
    rev3C[i,k,l,t] <= 0.10 * (Cap[k] + Cap[l]) * u3C[i,k,l,t];
