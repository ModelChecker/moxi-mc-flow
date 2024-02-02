#!/usr/bin/perl
#
#by Kristin Y. Rozier
#
#This software has been determined to be outside the scope of NASA NPG 2210 and therefore is not considered as controlled software.
#
#This program may be freely redistributed and/or modified under the terms of the enclosed software agreement. NASA is neither liable nor responsible for maintenance, updating, or correction of any errors in the software provided. Use of this software shall not be construed to constitute the grant of a license to the user under any NASA patent, patent application or other intellectual property.
#
#You should have received a software agreement along with this program. If not, please refer to Section 4 of: http://opensource.arc.nasa.gov/pdf/NASA_Open_Source_Agreement_1.3.txt
############################################################################
# LTLcounterLinear.pl
#
# Input: n = the number of bits in the counter
# 
# Output: an LTL formula describing an n-bit counter
#
# Purpose: Simplify the formula created by LTLcounter by reducing the number of 'next' operators using nesting.
#
# Usage: LTLcounterLinear.pl n
#
# Note: This program is simply an optimized version of LTLcounter.pl. It shares one extra 'X' in formula 3, two 'X's in formula 4, and formulates formulas 1 and 2 linearly (i.e X(a & X(a & X(a))) ) instead of exponentially (i.e. X(a) && X(X(a)) && X(X(X(a))) )

# System Description
#
# - 3 variables: 
#                m = marker
#                b = bits
#
# - the counter represents a sequence of n-bit strings in 2 variables
#   ex: n=4
#       m = 0001 0001 0001 0001 0001 0001 0001 0001 0001 0001 0001 0001 0001 0001
#       b = 0000 0001 0010 0011 0100 0101 0110 0111 1000 1001 1010 1011 1100 1101
#       m marks the least-significant bit
#       b is the sequence of bit-strings representing the counter
#
# - reverse bit order: in our actual LTL formula, we represent each n-length string 
#     in reverse order (left -> right : least -> most significant bit)
#   - the example above for n=4 becomes:
#       m = 1000 1000 1000 1000 1000 1000 1000 1000
#       b = 0000 1000 0100 1100 0010 1010 0110 1110
#
# - the LTL formula produced is true if the values of the two variables over time 
#     represent a proper n-bit counter



#################### Argument Setup ####################

#Check for correct number and type of command line arguments
if ($ARGV[0] =~ /^-v?/) {
    $verbose = 1;
    shift(@ARGV);
} #end if
else {
    $verbose = 0;
} #end else

if (@ARGV != 1) {
    die "Usage: LTLcounterLinear.pl n\n\tproduces a formula (linear in n) describing an n-bit counter\n\tUse flag -v for verbose, human-readable output.\n";
} #end if

$n = $ARGV[0]; 

#################### Generation of the Formula ####################
$pattern = ""; #make sure the pattern starts empty
$ppattern = ""; #make sure the printable pattern starts empty

#Here are the parts of the formula we know to be true:

#1)  The marker consists of a repeated pattern of a 1 followed by n-1 0's
$mpattern .= "(m) && ( [](m -> (NEST)))";
for ($i = 1; $i <= $n; $i++) {
    if ($i == $n) { $nest = "X(m)"; }
    else { $nest = "X(!m && NEST)"; }
    $mpattern =~ s/NEST/$nest/;
} #end for

$ppattern .= "1. $mpattern\n"; #just for now: add a return for readability
$pattern .= "($mpattern) && ";


#2) The bit is initially n 0's.
$bpattern = "(!b)NEST";
for ($i = 1; $i < $n; $i++) {
    $nest = " && X(!bNEST)"; 
    $bpattern =~ s/NEST/$nest/;
} #end for
$nest = "";
$bpattern =~ s/NEST/$nest/;

$ppattern .= "2. $bpattern\n"; #just for now: add a return for readability
$pattern .= "($bpattern) && ";


#3) If the least significant bit is 0, next time is is 1 and the other bits are the same.
$nestb0m1 = "!b";
$nestb1m1 = "b";
for ($i = 1; $i <= $n; $i++) {
    if ($i == $n) {
	$nestb0 = "X($nestb0m1)";
	$nestb1 = "X($nestb1m1)";
    } #end if
    else {
	$nestb0m1 = "X($nestb0m1)";
	$nestb1m1 = "X($nestb1m1)";
    } #end else
} #end for
$ppattern .= "3. []( (m && !b) -> ( X ( $nestb1m1 && ( ( (!m) && (b -> $nestb1) && (!b -> $nestb0) ) U m ) ) ) )\n";
#$pattern .= "([] (m -> ( (b -> ($nestb0)) && ((!b) -> ($nestb1)) ) ) ) && ";
$pattern .= "([]( (m && (!b)) -> ( X ( ($nestb1m1) && ( ( (!m) && (b -> ($nestb1)) && ((!b) -> ($nestb0)) ) U (m) ) ) ) )) && ";
#$pattern .= "([] ((m && (!b)) -> ( X ( ( ($nestb1m1) && (!m) && (b -> ($nestb1)) && ((!b) -> ($nestb0)) ) U (m) ) ) )) && ";


#4) For every n-length string in b, all of the bits through the first 0 will be flipped n steps later and every bit after that will remain unchanged. (This is the add one.)
$ppattern .= "4. [] ( (m && b) -> (X ($nestb0m1 && ( (b && !m && $nestb0) U (m || (!m && !b && X( $nestb1m1 && ( ( !m && (b -> $nestb1) && (!b -> $nestb0) ) U m ) ) ) ) ) ) ) )\n";
$pattern .= "([] ( (m && b) -> (X (($nestb0m1) && ( ((b) && (!m) && ($nestb0)) U ((m) || ((!m) && (!b) && (X( ($nestb1m1) && ( ( (!m) && ((b) -> ($nestb1)) && ((!b) -> ($nestb0)) ) U (m) ) )) ) ) ) ) ) ))";

if ($verbose == 1) {
    print "1) The marker consists of a repeated pattern of a 1 followed by n-1 0's then another 1\n";
    print "2) The bit is initially n 0's\n";
    print "3) If the least significant bit is 0, next time it is 1 and the other bits are the same.\n";
    print "4) For every n-length string in b, all of the bits through the first 0 will be flipped n steps later and every bit after that will remain unchanged. (This is the add one.)\n";
    print "Pattern: \n$ppattern\n";
} #end if

$pattern =~ s/\[\]/G/g;
$pattern =~ s/m/a/g;

if ($verbose == 1) {
    print "\nComputer readable: ";
} #end if
print "($pattern)\n";
