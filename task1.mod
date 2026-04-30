set VENUES;
set SPORTS;

param c {VENUES};        # fixed opening cost (thousand dollars)
param kappa {VENUES};    # max number of sports hosted at venue
param a {VENUES, SPORTS} binary;  # eligibility matrix

var y {i in VENUES} binary;                 # 1 if venue i is opened
var x {i in VENUES, j in SPORTS} binary;    # 1 if sport j assigned to venue i

minimize TotalCost:
    sum {i in VENUES} c[i] * y[i];

subject to OneVenuePerSport {j in SPORTS}:
    sum {i in VENUES} x[i,j] = 1;

subject to Eligibility {i in VENUES, j in SPORTS}:
    x[i,j] <= a[i,j];

subject to VenueCapacity {i in VENUES}:
    sum {j in SPORTS} x[i,j] <= kappa[i] * y[i];
