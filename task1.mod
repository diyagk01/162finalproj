set VENUES;
set SPORTS;

# Cost to open each venue (in thousands of dollars)
param c {VENUES};

# Maximum number of sports each venue can host
param kappa {VENUES};

# Eligibility: 1 if venue i can host sport j, 0 otherwise
param a {VENUES, SPORTS} binary;

# Decision variables
var y {i in VENUES} binary;              # 1 if venue i is opened
var x {i in VENUES, j in SPORTS} binary; # 1 if sport j is assigned to venue i

# Objective: minimize total venue opening cost
minimize TotalCost:
    sum {i in VENUES} c[i] * y[i];

# Each sport must be assigned to exactly one venue
subject to OneVenuePerSport {j in SPORTS}:
    sum {i in VENUES} x[i,j] = 1;

# A sport can only be assigned to a venue that is eligible to host it
subject to Eligibility {i in VENUES, j in SPORTS}:
    x[i,j] <= a[i,j];

# A venue can only host sports if it is opened, and it cannot exceed its capacity
subject to VenueCapacity {i in VENUES}:
    sum {j in SPORTS} x[i,j] <= kappa[i] * y[i];