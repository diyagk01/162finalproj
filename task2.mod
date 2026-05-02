set VENUES;
set SPORTS;
set WEEKS ordered;

# Cost to open each venue (in thousands of dollars)
param c {VENUES};

# Number of weeks each venue is available
param kappa {VENUES};

# Eligibility: 1 if venue i can host sport j, 0 otherwise
param a {VENUES, SPORTS} binary;

# Number of sessions required for each sport
param R {SPORTS};

# Decision variables
var y {i in VENUES} binary;                          # 1 if venue i is opened
var z {i in VENUES, j in SPORTS, t in WEEKS} binary; # 1 if sport j is scheduled at venue i in week t
var w {j in SPORTS, t in WEEKS} binary;              # 1 if sport j is assigned to week t

# Objective: minimize total cost of opening venues
minimize TotalCost:
    sum {i in VENUES} c[i] * y[i];

# Each sport must be scheduled in exactly one week
subject to OneWeekPerSport {j in SPORTS}:
    sum {t in WEEKS} w[j,t] = 1;

# If a sport is scheduled in a week, it must receive all required sessions in that week
subject to SessionsInChosenWeek {j in SPORTS, t in WEEKS}:
    sum {i in VENUES} z[i,j,t] = R[j] * w[j,t];

# A venue can host at most one sport per week, and only if it is opened
subject to VenueWeekCapacity {i in VENUES, t in WEEKS}:
    sum {j in SPORTS} z[i,j,t] <= y[i];

# A sport can only be scheduled at a venue if that venue is eligible
subject to Eligibility {i in VENUES, j in SPORTS, t in WEEKS}:
    z[i,j,t] <= a[i,j];

# A venue cannot be used beyond the number of weeks it is available
subject to WeekLimit {i in VENUES, j in SPORTS, t in WEEKS: ord(t) > kappa[i]}:
    z[i,j,t] = 0;