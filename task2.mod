set VENUES;
set SPORTS;
set WEEKS ordered;

param c {VENUES};        # fixed opening cost (thousand dollars)
param kappa {VENUES};    # number of weeks venue is available
param a {VENUES, SPORTS} binary;  # eligibility matrix
param R {SPORTS};        # required venue slots (sessions) per sport

var y {i in VENUES} binary;                        # 1 if venue i is opened
var z {i in VENUES, j in SPORTS, t in WEEKS} binary; # 1 if sport j at venue i in week t
var w {j in SPORTS, t in WEEKS} binary;            # 1 if sport j scheduled in week t

minimize TotalCost:
    sum {i in VENUES} c[i] * y[i];

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
