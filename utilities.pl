#!/usr/bin/perl
#Contributors: Jason Schuchardt and Matt Larson
#Last updated: 01/29/2021

use strict;
use warnings;
use Benchmark qw(:all);
use application "polytope";
use List::Util 'shuffle';
use List::Util qw(reduce);
use List::Compare;
use Algorithm::Combinatorics "subsets";
use PDL;
use PDL::Matrix;
use PDL::MatrixOps;

#contains functions that are not related to polymakes
#just useful perl functions 


#usage: cartesian_product(AoA)
#returns all pairs 
#not: don't input a reference 
sub cartesian_product {
	reduce {
    	[ map {
    		my $item = $_;
    		map [ @$_, $item ], @$a
    	} @$b ]
	} [[]], @_
}


#usage: round(number)
#round to the nearest integer
sub round{
	my $float = shift;
	my $rounded = int($float + $float/abs($float*2 || 1));
}

#usage: entrywiseEquality($aref, $aref);
#returns 1 if the array are the same size and have every entry equal
#returns 0 otherwise
#arrays must be arrays of numbers or strings
sub entrywiseEquality{
	my $a = shift;
	my @a = @{$a};
	my $b = shift;
	my @b = @{$b};
	if (scalar(@a) != scalar(@b)){
		return 0;
	}
	for my $i (0..scalar(@a) - 1){
		if ($a[$i] != $b[$i]){
			return 0;
		}
	}
	return 1;
}

#prints an array in a nice way
#useage: pArr($aref), where $aref is a reference to an array
sub pArr {
    my $aref = shift;
    print "[",join(", ",@{$aref}),"]\n";
}

#prints an array of arrays in a nice way
#usage: pArrArr($p), $p is a reference an array of references to arrays
sub pArrArr {
    my $aref = shift;
    print "[\n";
    for my $arrRef (@$aref) {
        print "[",join(", ",@{$arrRef}),"]\n";
    }
    print "]\n";
}

#power set
#note: takes array, returns array
sub subarrs {
    #if the input array is 0 return the empty list
    if (scalar(@_) == 0) {
        return ([]);
    }
    my $first = shift;
    my @rec = subarrs(@_);
    my @recp = map { my @temp = @{$_}; unshift @temp, $first; \@temp; } @rec;
    push(@rec, @recp);
    return @rec;
}


#returns 1 if n is even, -1 if n is odd
#i.e. (-1)^n 
#usage: powMinusOne(n);
sub powMinusOne {
    my $n = shift;
    if($n % 2) {
        return -1;
    }
    return 1;
}


#adds a number to the ith index of an array
#usage: addToIndex($aref, $i, $val)
#does not return anything, just modifies the array
#adds $val to ith spot in the array
sub addToIndex {
    my $aref = shift;
    my $i = shift;
    my $val = shift;
    if (not defined $aref->[$i]) {
        $aref->[$i]=0;
    }
    $aref->[$i] = $aref->[$i] + $val;
}


#returns a random vector of size $n with entries between 0 and 1
sub getRandomVector {
    my $len = shift;
    my @ans = ();
    for my $i (1..$len) {
        push(@ans, rand());
    }
    return \@ans;
}


#returns the sum of an array
#usage: sumArray(reference to array)
sub sumArray {
	my $arref = shift;
	my @array = @{$arref};
	my $sum = 0;
	my $size = scalar @array;
	for my $i (0..($size - 1)){
		$sum += $array[$i];
	}
	return $sum;
}

#usage: randomSubArray($array reference, size of desired subarray)
#generates a random sub array of the disired size
sub randomSubArray{
	my $aref = shift;
	my @array = @{$aref};
	my @shuffled = shuffle(@array);
	my $num = shift;
	if (scalar(@array) < $num) {
		return "Error: array too small"
	}
	my @new = @shuffled[0 .. $num - 1];
	return \@new;
}

#usage: union($aref1, $aref2)
#returns a reference to the union of the two arrays
#the arrays are distinct even if the entries are the same
sub union{
	my @a = @{shift @_};
	my @b = @{shift @_};
	my %union =  ();

	foreach my $e (@a) { $union{$e} = 1 }
	
	foreach my $e (@b) {
	    if ( not $union{$e} ) 
    		{ $union{$e} = 1}
    	}
    my @union = keys %union;
	return \@union;
}

#usage: vanishes($arref)
#returns an arref containing the places where the input is 0
sub vanishes{
	my $aref = shift;
	my @array = @{$aref};
	my @vanishing = ();
	for my $i (0 .. scalar(@array) - 1){
		if ($array[$i] == 0){
			push(@vanishing, $i)
		}
	}
	return \@vanishing;
}


#usage: isUnimodal(arref);
#checks if a SYMMETRIC array is unimodal
#returns 0 if it is not unimodal
sub isUnimodal{
	my $aref = shift;
	my @array = @{$aref};
	my $size = scalar(@array);
	my $num;
	if ($size % 2 == 0){
		$num = $size/2;
	}
	else{
		$num = ($size - 1)/2;
	}
	for my $i (0..$num - 1){
		if ($array[$i] > $array[$i + 1]){
			return 0;
		}
	}
	return 1;
}


#usage: removeDuplicates(AoA)
#takes an array of arrays of numbers
sub removeDuplicates{
	my $aoa = shift;
	my @aoa = @{$aoa};
	my %hash;
	my @result = ();
	for my $v (@aoa){
		my $str = "@{$v}";
		if (not $hash{$str}){
			$hash{$str} = 1;
			push(@result, $v);
		}
	}
	return \@result;
}


#usage: is_subset(sorted list, sorted list)
#checks if the second list is a subset of the first
#returns 1 if it is in the sublists
#returns 0 if it is not
#must be sorted!
sub is_subset{
	my @list = @{shift @_};
	my @sublist = @{shift @_};
	if (scalar(@sublist) == 0){
		return 1;
	}
	my $index = 0;
	for my $j (0..scalar(@list) - 1){
		if ($list[$j] > $sublist[$index]){
			return 0
		}
		elsif ($list[$j] == $sublist[$index]){
			$index += 1;
			if ($index == scalar(@sublist)){
				return 1;
			}
		}
	}
}

#usage: is_subset( list,  list)
#checks if the second list is a subset of the first
#returns 1 if it is in the sublists
#returns 0 if it is not
#sorts the lists initially
sub is_subset_unsorted{
	my @list = @{shift @_};
	@list = sort {$a <=> $b} @list;
	my @sublist = @{shift @_};
	@sublist = sort {$a <=> $b} @sublist;
	if (scalar(@sublist) == 0){
		return 1;
	}
	my $index = 0;
	for my $j (0..scalar(@list) - 1){
		if ($list[$j] > $sublist[$index]){
			return 0
		}
		elsif ($list[$j] == $sublist[$index]){
			$index += 1;
			if ($index == scalar(@sublist)){
				return 1;
			}
		}
	}
}

#usage: dot product of two arrays
#should be the same length
#returns the dot product
sub dot{
	my @a = @{shift @_};
	my @b = @{shift @_};
	if (scalar @a != scalar @b){
		print "Not same length";
	}
	my $sum = 0;
	for my $i (0..scalar(@a) - 1){
		$sum = $sum + $a[$i] * $b[$i];
	}
	return $sum;
}

#usage: AoAUnion($Aoa, $AoA)
#returns the union of the two arrays, where if two arrays in the AoA are entrwise equal then they are viewed as the same
#returns an AoA
sub AoAUnion{
    my ($a1, $a2) = @_;
    my %uniq;

    $uniq{"@$_"} = 1 for @$a1;

    for ( @$a2 ) {
        my $key = "@$_";
        next if $uniq{$key}++;
        push @$a1, [ @$_ ];
    }

    return $a1;

}
#usage:dotProduct($aref, $aref)
#arefs should be the same length
#computes the dot product
sub dotProduct{
	my $vec1 = shift;
	my $vec2 = shift;
	my $answer = 0;
	for my $i (0..(scalar(@{$vec1}) - 1)){
		$answer += ($vec1->[$i])*($vec2->[$i]);
	}
	return $answer;
}




