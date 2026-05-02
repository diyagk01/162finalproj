set VENUES;
set SPORTS;
set WEEKS ordered;

# parameters
param c     {VENUES};            # fixed opening cost (1000s $)
param Cap   {VENUES};            # seating capacity (1000s of seats)
param kappa {VENUES};            # num of weeks venue is available
param a     {VENUES, SPORTS} binary;   # eligibility matrix
param D     {SPORTS};            # demand / session (thousands of tickets)
param R     {SPORTS};            # required sessions / sport
param p := 10;                   # profit per ticket ($), so 10*(thousand tickets) = thousand $

param m {i in VENUES, j in SPORTS} := min(D[j], Cap[i]);

# DV
var y {i in VENUES} binary;                          # 1 if venue i is opened
var z {i in VENUES, j in SPORTS, t in WEEKS} binary; # 1 if sport j has a session at venue i in week t
var w {j in SPORTS, t in WEEKS} binary;              # 1 if sport j is scheduled in week t

# Obj Func
minimize NetCost:
    sum {i in VENUES} c[i] * y[i]
  - p * sum {i in VENUES, j in SPORTS, t in WEEKS} m[i,j] * z[i,j,t];

# Contraints

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
