#!/usr/bin/perl

# LTLcounter.pl
#
# Input: n = the number of bits in the counter
# 
# Output: an LTL formula describing an n-bit counter
#
# Usage: LTLcounter.pl n
#

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
    die "Usage: LTLcounter.pl n\n\tproduces a formula describing an n-bit counter\n\tUse flag -v for verbose, human-readable output.\n";
} #end if

$n = $ARGV[0];

#################### Generation of the Formula ####################
$pattern = ""; #make sure the pattern starts empty
$ppattern = ""; #make sure the printable pattern starts empty

#Here are the parts of the formula we know to be true:

#1)  The marker consists of a repeated pattern of a 1 followed by n-1 0's
$mpattern .= "(m) && ( [](m -> (";
for ($i = 1; $i <= $n; $i++) {
    if ($i == $n) { $nest = "m"; }
    else { $nest = "!m"; }
    for ($j = 0; $j < $i; $j++) {
	$nest = "X($nest)";
    } #end for
    if ($i == $n) { $mpattern .= "$nest)))"; }
    else { $mpattern .= "($nest) && ";}
} #end for

$ppattern .= "1. $mpattern\n"; #just for now: add a return for readability
$pattern .= "($mpattern) && ";


#2) The bit is initially n zeros
$bpattern = "(!b)";
for ($i = 1; $i < $n; $i++) {
    $nest = "!b";
    for ($j = 0; $j < $i; $j++) {
	$nest = "X($nest)";
    } #end for
    $bpattern .= " && ($nest)";
} #end for
$ppattern .= "2. $bpattern\n"; #just for now: add a return for readability
$pattern .= "($bpattern) && ";


#3) If the least significant bit is 0, next time is is 1 and the other bits are the same
$nestb0 = "!b";
$nestb1 = "b";
for ($i = 1; $i <= $n; $i++) {
    $nestb0 = "X($nestb0)";
    $nestb1 = "X($nestb1)";
} #end for
$ppattern .= "3. []( (m && !b) -> ( $nestb1 && X ( ( (!m) && (b -> $nestb1) && (!b -> $nestb0) ) U m ) ) )\n";
#$pattern .= "([] (m -> ( (b -> ($nestb0)) && ((!b) -> ($nestb1)) ) ) ) && ";
$pattern .= "([] ((m && (!b)) -> ( ($nestb1) && (X ( ( (!m) && (b -> ($nestb1)) && ((!b) -> ($nestb0)) ) U (m) ) ) ))) && ";


#4) For every n-length string in b, all of the bits through the first 0 will be flipped n steps later and every bit after that will remain unchanged. (This is the add one.)
$ppattern .= "4. [] ( (m && b) -> ($nestb0 && (X ( (b && !m && $nestb0) U (m || (!m && !b && $nestb1 && X( ( !m && (b -> $nestb1) && (!b -> $nestb0) ) U m ) ) ) ) ) )\n";
$pattern .= "([]( (m && b) -> (($nestb0) && (X ( (b && (!m) && ($nestb0)) U (m || ((!m) && (!b) && ($nestb1) && ( X( ( (!m) && (b -> ($nestb1)) && ((!b) -> ($nestb0)) ) U m ) ) ) ) ) ) ) ) )";

if ($verbose == 1) {
#    print "1) The marker consists of a repeated pattern of a 1 followed by n-1 0's then another 1\n";
    print "1) The marker consists of a repeated pattern of a 1 followed by n-1 0's.\n";
#    print "2) The bit is initially n 0's\n";
    print "2) The first n bits are 0's.\n";
#    print "3) If the least significant bit is 0, next time it is 1 and the other bits are the same.\n";
    print "3) If the least significant bit is 0, then it is 1 n steps later 
   and the other bits do not change.\n";
#    print "4) For every n-length string in b, all of the bits through the first 0 will be flipped n steps later and every bit after that will remain unchanged. (This is the add one.)\n";
    print "4) All of the bits before and including the first 0 in an n-bit block flip their values in the next block; the other bits do not change.\n";
    print "Pattern: \n$ppattern\n";
} #end if

$pattern =~ s/\[\]/G/g;
$pattern =~ s/m/a/g;

if ($verbose == 1) {
    print "\nComputer readable: ";
} #end if
print "($pattern)\n";
