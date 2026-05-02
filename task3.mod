### Task 3: Multi-week scheduling with ticket-sales revenue ###

set VENUES;
set SPORTS;
set WEEKS ordered;

# --- Parameters ---
param c     {VENUES};            # fixed opening cost (thousand $)
param Cap   {VENUES};            # seating capacity (thousands of seats)
param kappa {VENUES};            # number of weeks venue is available
param a     {VENUES, SPORTS} binary;   # eligibility matrix
param D     {SPORTS};            # demand per session (thousands of tickets)
param R     {SPORTS};            # required sessions per sport
param p := 10;                   # profit per ticket ($), so 10*(thousand tickets) = thousand $

# Tickets sold per session of sport j held at venue i (thousands).
# Capacity-limited when demand exceeds capacity.
param m {i in VENUES, j in SPORTS} := min(D[j], Cap[i]);

# --- Decision variables ---
var y {i in VENUES} binary;                          # 1 if venue i is opened
var z {i in VENUES, j in SPORTS, t in WEEKS} binary; # 1 if sport j has a session at venue i in week t
var w {j in SPORTS, t in WEEKS} binary;              # 1 if sport j is scheduled in week t

# --- Objective: minimize fixed costs minus ticket revenue ---
minimize NetCost:
    sum {i in VENUES} c[i] * y[i]
  - p * sum {i in VENUES, j in SPORTS, t in WEEKS} m[i,j] * z[i,j,t];

# --- Constraints (same scheduling logic as Task 2) ---

# Each sport is scheduled in exactly one week.
subject to OneWeekPerSport {j in SPORTS}:
    sum {t in WEEKS} w[j,t] = 1;

# In the chosen week, the sport must have R[j] sessions across distinct venues.
subject to SessionsInChosenWeek {j in SPORTS, t in WEEKS}:
    sum {i in VENUES} z[i,j,t] = R[j] * w[j,t];

# A venue can host at most one sport per week, and only if it is opened.
subject to VenueWeekCapacity {i in VENUES, t in WEEKS}:
    sum {j in SPORTS} z[i,j,t] <= y[i];

# A sport can only be held at an eligible venue.
subject to Eligibility {i in VENUES, j in SPORTS, t in WEEKS}:
    z[i,j,t] <= a[i,j];

# Venue i can only operate in weeks 1..kappa[i].
subject to WeekLimit {i in VENUES, j in SPORTS, t in WEEKS: ord(t) > kappa[i]}:
    z[i,j,t] = 0;
