#!/usr/bin/perl
#Contributors: Jason Schuchardt and Matt Larson
#Last updated: 08/17/2019

#contains various useful scripts
#does not have specific things designed to test specific conjectures


use strict;
use warnings;
use Benchmark qw(:all);
use application "polytope";
use List::Util 'shuffle';
use Parallel::Loops;
use List::Compare;
use Algorithm::Combinatorics "subsets";
use PDL;

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


#useage: standard_simplex_vertices(n);
#returns a reference to an array that contains a reference to the 
#vertices of the standard simplex, i.e.
#(1, 0, 0,0) of length n + 1
#standard simplex has n + 1 vertices
sub standard_simplex_vertices {
    my $n = shift(@_);
    my (@vert_arr, @temp_arr);
    #@vert_arr = array that stores the vertices
    for my $i (0..$n) {
        $temp_arr[$i]=0;
    }
    #creates temporary array of all 0's
    for my $i (0..$n) {
        my @copy = @temp_arr;
        $copy[$i] = 1;
        push @vert_arr, \@copy;
    }
    #goes through the n + 1 entries in the array
    #changes one entry to 1
    #store a reference to this new array in @vert_arr
    return \@vert_arr;
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


sub standard_simplex {
    my $n = shift;
    return new Polytope(POINTS => standard_simplex_vertices($n));
}


#takes a subdivision and a face
#returns the restriction to that face
sub restriction {
    my $subdiv = shift;
    my $n = $subdiv->DIM;
    my @face = @{shift @_}; # face is an arrref of vertices on face.
                            # vertices are given by their index from 0 to $n 
    #pArr \@face;
    my @faceComplement = grep { my $v = $_; not(grep { $v == $_ } @face); } (0..$n);
    #pArr \@faceComplement;
    my $onface = sub {
        # takes an arrRef and returns true if the point with those coords is on the face given by $face.
        my $aref = shift;
        for my $i (@faceComplement) {
            if ($aref->[$i] != 0) {
                return 0;
            }
        }
        return 1;
    };
    my $indices = $subdiv->VERTEX_INDICES;
    #pArr($indices);
    my $coords = $subdiv->COORDINATES;
    #pArrArr($coords);
    my $taggedcoords = []; #[map { [$_,$coords->[$_]] } @{$indices}];
    for my $i (0..$#{ $indices }) {
        $taggedcoords->[$i]=[$i,$coords->[$indices->[$i]]];
    }
    # find the vertices on the face
    #pArrArr($taggedcoords);
    my $tCoordsOnFace = [ grep { &{$onface}(@{$_}[1]); } @{$taggedcoords} ];
    my $coordsOnFace = [ map { @{$_}[0]; } @{$tCoordsOnFace} ];
    #pArr($coordsOnFace);
    my $ans = Polymake::topaz::induced_subcomplex($subdiv, $coordsOnFace); # forgets the geometry
    return $ans;
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


#finds all integral points on n*standard (dim - 1) simplex
#usage: getNRationalPoints(n, dim)
#returns a reference to an array of the integral points, in the form of an array
sub getNRationalPoints {
    my $n = shift;
    my $dim = shift; # dimension of ambient space not simplex.
    if ($n < 0) {
        return [];
    }
    if ($dim==0) {
        return ($n==0)?[[]]:[];
    }
    if ($dim==1) {
        return [[$n]];
    }
    my @pts = ();
    for my $i (0..$n) {
        for my $pt (@{getNRationalPoints($n-$i, $dim-1)}) {
            push(@{$pt}, $i);
            push(@pts, $pt);
        }
    }
    return \@pts;
}



#finds all rational points on the boundary of $n*standard (dim - 1) simplex
#returns in the form of array of arrays
sub getBoundaryNRationalPointsRec {
    my $n = shift;
    my $dim = shift; # dimension of ambient space not simplex.
    if ($n < 0) {
        return [];
    }
    if ($dim==0) {
        return ($n==0)?[[]]:[];
    }
    if ($dim==1) {
        return ($n==0)?[[0]]:[];
    }
    my @pts = ();
    for my $pt (@{getNRationalPoints($n, $dim-1)}) {
        push(@{$pt},0);
        push(@pts, $pt);
    }
    for my $i (1..$n) {
        for my $pt (@{getBoundaryNRationalPointsRec($n-$i, $dim-1)}) {
            push(@{$pt}, $i);
            push(@pts, $pt);
        }
    }
    return \@pts;
}

#finds all points on the boundary on n* standard (dim - 1) simplex
#returns as a matrix
sub getBoundaryNRationalPoints {
	my $n = shift;
    my $dim = shift;
    return new Matrix<Rational>(getBoundaryNRationalPointsRec($n,$dim));
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

#converts to Barycentric coords by normalizing so that the sum is 1
sub toBarycentricCoords {
    my @arr = @{shift @_};
    my $sum = 0;
    for my $val (@arr) {
        $sum += $val;
    }
    return [ map( new Rational($_) / ($sum),   @arr) ]
}


#the vertices of the simplex need to be included in the points
#usage: regularSubdivisionOfStandardSimplex(coord ref, weightref)
sub regularSubdivisionOfStandardSimplex { 
    my @coords = @{shift @_};
    my $weightsRef = new Vector<Rational>(shift @_);
    #converts the coordinant vector to barycentric coords
    my @baryCoords = map { toBarycentricCoords($_); } @coords;
    my $baryMat=new Matrix<Rational>(\@baryCoords);
    return new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat,
        INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
}

sub randomRegularSubdivOfStandardSimplex {
    my $coordsRef = shift;
    my $weightsRef = getRandomVector(scalar(@{$coordsRef}));
    return regularSubdivisionOfStandardSimplex($coordsRef, $weightsRef);
}

sub totallyRandomRegularSubdivOfStandardSimplex {
    my $dSimplex = shift;
    my $n = shift;
    my $coordsRef = getNRationalPoints($n, ($dSimplex + 1));
    my $weightsRef = getRandomVector(scalar(@{$coordsRef}));
    return regularSubdivisionOfStandardSimplex($coordsRef, $weightsRef);
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



# computes as alternating sum of H_VECTORs
sub local_h {
    my $subdiv = shift; # subdivision of a standard simplex of the appropriate dimension
    my $n = $subdiv->DIM;
    my $d = $n+1;
    my $ans = [];
    for my $face (subarrs(0..$n)) {
        if (scalar(@{$face}) == 0) {
            addToIndex($ans,0,powMinusOne($d));
        } else {
            my $rest = restriction($subdiv,$face);
            my @hvect = @{$rest->H_VECTOR};
            #pArr(\@hvect);
            for my $i (0..$#hvect) {
                addToIndex($ans, $i, powMinusOne($n-$rest->DIM)*$hvect[$i]);
            }
        }
    }
    return $ans;
}


#usage: isCone(subdivision)
#checks if the subdivision is a cone over a face
sub isCone {
	#print "isCone start";
    my $subdiv = shift;
    my $n = $subdiv->DIM;
    my $indices = $subdiv->VERTEX_INDICES;
    my $nverts = $subdiv->N_VERTICES;
    my $coords = $subdiv->COORDINATES;
    my $taggedcoords = []; #[map { [$_,$coords->[$_]] } @{$indices}];
    for my $i (0..$#{ $indices }) {
        $taggedcoords->[$i]=[$i,$coords->[$indices->[$i]]];
    }
    for my $i (0..$n){
	    my $onface = sub {
	        # takes an arrRef and returns true if the point with those coords is on the face given by $face.
	        my $aref = shift;
	        if ($aref->[$i] != 0) {
	            return 0;
	        }
	        return 1;
	    };
	    my $tCoordsOnFace = [ grep { &{$onface}(@{$_}[1]); } @{$taggedcoords} ];
	    if (scalar(@{$tCoordsOnFace})==$nverts-1){
	    	#print "isCone end";
	    	return 1;
	    }
    }
    #print "isCone end";
    return 0;
 }



#usage: printSubdiv(subdivision)
#prints F vector, H vector, local H vector, facets, vertex coordinants 
sub printSubdiv {
	my $subdiv= shift;
	print "F vector: ", $subdiv->F_VECTOR,"\n";
	print "H vector: ", $subdiv->H_VECTOR,"\n";
	print "local h vector: ";
	pArr(local_h($subdiv));
	print "\n";
	print "Facets: \n", $subdiv->FACETS,"\n";
	print "Vertex coords:\n";
	for my $i (0..$#{$subdiv->VERTEX_INDICES}) {
		print "$i: ";
		pArr($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$i]]);
	}
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






#usage generateABunchQuick(dimension, n, iterations, number of points to lift)
#randomly lifts numpoints of the points on n*standard dim simplex
sub generateABunchQuick{
	my $dim = shift;
	my $n = shift;
	my $iter = shift;
	my $numpoints = shift;
	my @ans = ();
	#computing a regular subdivision requires the vertices of the simplex
	#to be among the points 
	my $boundary_points = getBoundaryNRationalPointsRec($n,$dim+1);
	my $must_have = standard_simplex_vertices($dim);
	#removes the vertices from candidates
	my $count_zeros = 0;
	my $index = 0;
	while ($index < scalar(@{$boundary_points})){
		$count_zeros = 0;
		for my $k (0..($dim)){
			if (($boundary_points->[$index]->[$k]) == 0){
				$count_zeros += 1;
			}
		}
		if ($count_zeros == $dim){
			splice(@{$boundary_points}, $index, 1 );
		} else{
			$index++;
		}
}

	for my $i (1..$iter) {
		#randomly choses a subset
		my @rcoords = @{randomSubArray($boundary_points, $numpoints)};
		#adds back in the vertices
		my @baryCoords = map { toBarycentricCoords($_); } @rcoords;
		my $points = union($must_have, \@baryCoords);
		my $baryMat=new Matrix<Rational>($points);
		my $rsub = randomRegularSubdivOfStandardSimplex($baryMat);
		my $lh = local_h($rsub);
		if(sumArray($lh) == 0) {
			push(@ans, $rsub);
		} 
		print "on iteration $i, found ", scalar(@ans), "\n";
	}
	return \@ans;

}


#usage: countDuplicates(Array of subdivisions, as geometric simplicial complices)
#returns the number of order pairs where the underlying abstract simplicial complexes are isomorphic
sub countDuplicates{
	my $dupes = 0;
	my $aref = shift;
	my @arr1 = @{$aref};
	my @array = ();
	#converts to abstract simplicial complexes
	for my $k (0..(scalar(@arr1) - 1)){
		push @array, (new topaz::SimplicialComplex($arr1[$k]));
	}
	for my $i (0..(scalar(@array) - 1)){
		for my $j ($i + 1..(scalar(@array) - 1)){
			if (topaz::isomorphic($array[$i], $array[$j])){
				print "Subdivision ", $i, " is maybe the same as subdivision ", $j, "\n";
				$dupes++;
			}
		}
	}
	print "Total number of duplicates:", $dupes;
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

#usage: vectorToArray($vector)
#returns reference to array of that vector
sub vectorToArray{
	my $vec = shift;
	my @array = @{$vec};
	return \@array;
}

#usage: internalKSkeleton($subiv, $k)
#returns an abstract simplicial complex
#returns the abstract simplcial complex that is the closure of the internal k-faces
#uses the fact that a face is interior iff the vertices of the face do not all have some
#coordinant that vanishes
sub internalKSkeleton{
	my $comp = shift;
	my $k = shift;
	my $dim = $comp->DIM;
	my $abs = new topaz::SimplicialComplex($comp);
	my $overall_k_skeleton = new topaz::SimplicialComplex(topaz::k_skeleton($abs, $k));
	my $facet_list_temp2 = $overall_k_skeleton->FACETS;
	#array containing facets
	my @facet_list_temp1 = @$facet_list_temp2;
	my $num_facets = scalar(@facet_list_temp1);
	my @facet_list = map(vectorToArray($facet_list_temp1[$_]), (0..$num_facets - 1));
	#array containing the coordinants of the vertices
	my @vertices_temp = map($comp->COORDINATES->[$comp->VERTEX_INDICES->[$_]], (0..$comp->N_VERTICES - 1));
	my $num_vert = scalar(@vertices_temp);
	my @vertices = map(vectorToArray($vertices_temp[$_]), (0..$num_vert - 1));
	#for each vertex, makes an array of places where it vanishes
	my @vanish_list = map(vanishes($vertices[$_]), (0..$num_vert - 1));
	my @internal_facets = ();
	#for each facet, checks if the intersection of the vanish coordinants is empty
	for my $i (0..$num_facets - 1){
		my @list_of_vanishing = ();
		for my $j (0..$k){
			push(@list_of_vanishing, $vanish_list[${$facet_list[$i]}[$j]]);
		}

		my $lc = List::Compare->new(@list_of_vanishing);

		if (scalar($lc->get_intersection) == 0){
			push(@internal_facets, $facet_list[$i]);
		}
	}
	my $s = new topaz::SimplicialComplex(INPUT_FACES=>\@internal_facets);
	return $s;
}




#usage: generateSubdivQuick(dimension, n, number, number of points to lift)
#generates number subdivisions, returns as an arref
sub generateSubdivQuick{
	my $dim = shift;
	my $n = shift;
	my $iter = shift;
	my $numpoints = shift;
	my @ans = ();
	#computing a regular subdivision requires the vertices of the simplex
	#to be among the points 
	my $boundary_points = getBoundaryNRationalPointsRec($n,$dim+1);
	my $must_have = standard_simplex_vertices($dim);
	#removes the vertices from candidates
	my $count_zeros = 0;
	my $index = 0;
	while ($index < scalar(@{$boundary_points})){
		$count_zeros = 0;
		for my $k (0..($dim)){
			if (($boundary_points->[$index]->[$k]) == 0){
				$count_zeros += 1;
			}
		}
		if ($count_zeros == $dim){
			splice(@{$boundary_points}, $index, 1 );
		} else{
			$index++;
		}
}

	for my $i (1..$iter) {
		#randomly choses a subset
		my @rcoords = @{randomSubArray($boundary_points, $numpoints)};
		#adds back in the vertices
		my @baryCoords = map { toBarycentricCoords($_); } @rcoords;
		my $points = union($must_have, \@baryCoords);
		my $baryMat=new Matrix<Rational>($points);
		my $rsub = randomRegularSubdivOfStandardSimplex($baryMat);
		push(@ans, $rsub);
	}
	return \@ans;
}








#usage: carrier($subdivision of standard simplex, array of vertices on subdivision)
#returns a list of coordinant vectors on which the face is NOT supported
sub carrier{
	my $subdiv = shift;
	my $face = shift;
	my @face = sort {$a <=> $b} @{$face};
	my $num_vert = scalar(@face);
	if ($num_vert == 0){
		return [0..$subdiv->DIM];
	}
	if ($num_vert == 1){
		return vanishes($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$face[0]]]);
	}
	my @list_of_vanishing = ();
	#printSubdiv($subdiv);
	for my $i (0...$num_vert - 1){
		push(@list_of_vanishing, vanishes($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$face[$i]]]));
	}
	#pArrArr(\@list_of_vanishing);
	my $lc = List::Compare->new(@list_of_vanishing);
	my @intersection = $lc->get_intersection;
	@intersection = sort {$a <=> $b} @intersection;
	return \@intersection;
}

#usage: excess(subdivision, array of vertices of the subdivision)
#returns the excess of the face
sub excess{
	my $subdiv = shift;
	my $dim = $subdiv->DIM;
	my $face = shift;
	my $image_dim = $dim  - scalar(@{carrier($subdiv, $face)});
	#print("Image dimension is: ", $image_dim, "\n");
	my $excess = $image_dim - (scalar(@{$face}) - 1);
	return $excess;
}




#usage: reindex(complex, set), with the entries of the set being less than the number of vertices
#returns an array containing the vertex labels of the set
#reindexes by vertex labels
sub reindex{
	my $comp = shift;
	my $set = shift;
	my @set = @{$set};
	my $labels = $comp->VERTEX_LABELS;
	my @labels = @{$labels};
	my @output = map($labels[$_], @set);
	return \@output
}

#usage: relativeLocalH($subdiv, $E)
#computes relative local h
#face needs to be in increasing order
sub relLocalH{
	my $subdiv = shift;
	my $n = $subdiv->DIM;
	my $E = shift;
	my $lh = new UniPolynomial("0*x");
    my @E = @{$E};
    my $sizeE = scalar(@E);
    my $E_set = new Set<Int>(@E);
    my $link;
    if ($sizeE == 0){
    	$link = $subdiv;
        }
    else{
    	$link = new topaz::GeometricSimplicialComplex(topaz::link_complex($subdiv, $E));
    }
    #creates array of the faces
    my $diagram = $link->HASSE_DIAGRAM;
    my $face_list = $diagram->FACES;
    my @face_list = @{$face_list};
    shift(@face_list);
    my @face_list2 = map(vectorToArray($_), @face_list);
    my @face_list3 = map(reindex($link, $_), @face_list2);
    #sums over faces using excess formula
    for my $face (@face_list3){
    	my $ex = excess($subdiv, union($E, $face));
    	my $sign = powMinusOne($n + 1 - scalar(@{$face}) - $sizeE);
    	my $p = new UniPolynomial("($sign)*((x-1)^($ex))*(x^($n + 1 - $sizeE - $ex))");
    	$lh = $lh + $p;
    }
    #need to extract coefficients in a good way
    #print $lh, "\n";
    my $dumb = new UniPolynomial("1 - x^($n + 2 - $sizeE)");
    my $dumb2 = new UniPolynomial("1 - x");
    my $dumb3 = numerator($dumb/$dumb2);
    $lh = $lh + $dumb3;
    my $temp_vec = $lh->coefficients_as_vector;
    my $ordering = $lh->monomials_as_vector;
    my @ans;
    for my $j (0..($temp_vec->dim - 1)){
    	$ans[$ordering->[$j]] = ($temp_vec->[$j] - 1);
    }
    return \@ans;


}

#usage: checkMaximalFace(complex, arref of vertices of a facet)
#checks if a codimension 1 face of the maximal face has excess 0
#returns 1 if the facet is non-pyramidal, 0 if it is a pyramid
sub checkMaximalFace{
	my $subdiv = shift;
	my $facet = shift;
	my @facet = @{$facet};
	my $n = scalar(@facet);
	for my $i (0..$n - 1){
		my @temp = @facet;
		splice(@temp, $i, 1);
		if (excess($subdiv, \@temp) == 0){
			return 0;
		}
	}
	return 1;
}

#usage: checkAllMaximalFaces(subdivision)
#checks if all maximal faces are a pyramid
sub checkAllMaximalFaces{
	my $subdiv = shift;
	my $flist = $subdiv->FACETS;
	my $num = $flist->size;
	for my $i (0..$num - 1){
		if (checkMaximalFace($subdiv, $flist->[$i]) == 1){
			return 1;
		}
	}
	return 0;
}






#usage: reindex(complex, set), with the entries of the set being less than the number of vertices
#returns an array containing the vertex labels of the set
#reindexes by vertex indices
sub reindexIndices{
	my $comp = shift;
	my $set = shift;
	my @set = @{$set};
	my $labels = $comp->VERTEX_INDICES;
	my @labels = @{$labels};
	my @output = map($labels[$_], @set);
	return \@output
}




#usage: isUnimodal(arref);
#checks if a SYMMETRIC array is 
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




#usage: returnNonPyramidalFaces($subiv)
#returns an arref containing all non-pyramidal facets
sub returnNonPyramidalFaces{
	my $subdiv = shift;
	my @flist = ();
	my $num_facets = $subdiv->N_FACETS;
	for my $i (0..$num_facets - 1){
		if (checkMaximalFace($subdiv, \@{$subdiv->FACETS->[$i]}) == 1){
			push(@flist, \@{$subdiv->FACETS->[$i]});
		}
	}
	return(\@flist);
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


#usage: isFace($simplicial complex, $aref)
#$aref is interpreted as a possible face of the simplicial complex
#returns 1 if it is a face
#returns 0 if it is not
sub isFace{
	my $simp = shift;
	my $face_u = shift;
	#sorts face
	my @face = sort {$a <=> $b} @{$face_u};
	my $size = scalar(@face);
	#iterates through the facets. returns 1 if it finds the face
	my $facets = $simp->FACETS;
	my $num = $simp->N_FACETS;
	for my $i (0..$num - 1){
		my $facet = $facets->[$i];
		my @facet = @{$facet};
		my $index = 0;
		for my $j (0..scalar(@facet) - 1){
			if ($facet[$j] > $face[$index]){
				last;
			}
			elsif ($facet[$j] == $face[$index]){
				$index += 1;
				if ($index == $size){
					return 1;
				}
			}
		}

	}
	return 0;
}


#usage: printLocalHCarrier($subdiv)
#takes a subdivisions, finds all non-pyramidal facets
#prints computes the carrier, prints local h
sub printLocalHCarrier{
	my $subdiv = shift;
	my $flist = returnNonPyramidalFaces($subdiv);
	my @flist = @{$flist};
	my @toconsider = ();
	for my $j (0..scalar(@flist) - 1){
		#creates array of faces, gets rid of the empty set and whole facet
		my @facet = @{$flist[$j]};
		my @faces = subarrs(@facet);
		shift(@faces);
		pop(@faces);
		push(@toconsider, @faces);
	}
	my @f = @{removeDuplicates(\@toconsider)};
	for my $face (@f){
		if (scalar(@{$face}) + excess($subdiv, $face) - 1 < $subdiv->DIM - 1){
			print "On face: "; 
			pArr($face);
			print "The carrier has dimension ", (scalar(@{$face}) + excess($subdiv, $face) - 1), " local h is ";
			pArr(relativeLocalH($subdiv, $face));

			}
		}
	
}
#usage: relativeLocalH(subdivision, facet)
#computes relative local h as a sum of alternating h-vectors
#hopefully much faster
sub relativeLocalH{
	my $subdiv = shift;
    my $n = $subdiv->DIM;
    my $d = $n+1;
    my $E = shift;
    my @E = @{$E};
    my $E_size = scalar(@{$E});
    my $link;
    if (scalar(@{$E}) == 0){
    	$link = $subdiv;	
    }
    else{	
    	$link = new topaz::SimplicialComplex(topaz::link_complex($subdiv, $E));
    }
    my $num = $link->N_VERTICES;
    my $includable = carrier($subdiv, $E);
    #creates a hash for each subset, 
    my %face_to_vert;
    my @subsets = subsets($includable);
    for my $verts (@subsets){
    	$face_to_vert{"@{$verts}"} = [];
    }

    #loops through the vertices, finds out what face it is carried on of those contained in the carrier
    #adds the vertex to right places in the hash
    for my $i (0..$num - 1){
    	my $c = carrier($subdiv, [$link->VERTEX_LABELS->[$i]]);
    	my $lc = List::Compare->new($c, $includable);
    	my @intersection = $lc->get_intersection;
    	my @others = $lc->get_complement;
    	my @toadd = subsets(\@intersection);
    	for my $extra (@toadd){
    		my @final = @others;
    		push(@final, @{$extra});
    		@final = sort {$a <=> $b} @final;
    		push(@{$face_to_vert{"@final"}}, $i);
    	}
    }

    my $ans = [];
    for my $face (@subsets){
    	my $verts = $face_to_vert{"@{$face}"};
    	if (scalar(@{$verts}) == 0){
    		addToIndex($ans, 0, powMinusOne($d - $E_size));
    		next;
    	}
    	my $restriction = new topaz::SimplicialComplex(topaz::induced_subcomplex($link, $verts));
    	my @hvect = @{$restriction->H_VECTOR};
    	for my $i (0..scalar(@hvect - 1)){
    		addToIndex($ans, $i, powMinusOne($d-($restriction->DIM + $E_size + 1))*$hvect[$i]);
    	}
    }

    return $ans;
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

#usage: excessInternalFaces($subdiv, k, l)
#returns the excess of all the l-faces of the internal k-skeleton
sub excessInternalFaces{
	my $subdiv = shift;
	my $k = shift;
	my $l = shift;
	my $skel = internalKSkeleton($subdiv, $k);
	if ($skel->N_VERTICES == 0){
		return 0;
	}
	my $faces = new topaz::SimplicialComplex(topaz::k_skeleton($skel, $l));
	my $facet_list = $faces->FACETS;
	my @facet_list = @{$facet_list};
	my @facet_list2 = map(vectorToArray($_), @facet_list);
	my @facet_list3 = map(reindexIndices($skel, $_), @facet_list2);
	for my $face (@facet_list3){
		print excess($subdiv, $face), "\n";
	}
}



#usage: hProjection($aref, k)
#finds the point on k*standard simplex such that $aref (treated as a point) is taken to that point by homeothy
#returns as aref
sub hProjection{
	my $point = shift;
	my @point = @{$point};
	my $k = new Rational(shift);
	my $sum = new Rational(sumArray(\@point));
	my $scale = $k/$sum;
	my @result = map($point[$_]*$scale, (0..scalar(@point) - 1));
	return \@result;
}


#usage:uniformRND($dim, $cbound, $gbound, $num)
#generates a random newton diagram in dimension $dim
#guarantees that the newton diagram is convenient
#adds random multiples of standard basis vectors up to $cbound
#adds $num random points, each coordinant non-negative integer up to $gbound
#returns AoAs containing the points
sub uniformRND{
	my $dim = shift;
	my $cbound = shift;
	my $gbound = shift;
	my $num = shift;
	my @output = ();
	#adds points to force convenience
	for my $i (0..$dim - 1){
		my @vec = (0) x ($dim);
		addToIndex(\@vec, $i, int(rand($cbound - 1) + 1));
		push(@output, \@vec);
	}

	#adds other points
	for my $i (0..$num - 1){
		my @vec = (0) x ($dim - 1);
		for my $j (0 .. $dim - 1){
			addToIndex(\@vec, $j, int(rand($gbound)));
		}
		if (sumArray(\@vec) > 0){
			push(@output, \@vec);
		}
	}
	#removes points that have the same projection
	#keeps a random point
	my @final = ();
	my @proj = map(hProjection($_, 1), @output);
	my %hash;
	for my $i (0.. scalar(@proj) - 1){
		my $str = "@{$proj[$i]}";
		if (not $hash{$str}){
			$hash{$str} = 1;
			push(@final, $output[$i]);
		}
	}

	return \@final;
}

#usage: sumRND($dim, $cbound, $sum, $num)
#generates a random newton diagram in dimension $dim
#guarantees that the newton diagram is convenient
#adds random multiples of standard basis vectors up to $cbound
#adds $num random points, forces the coordinates to sum to a random number between 1 and sum
#returns AoAs containing the points
sub sumRND{
	my $dim = shift;
	my $cbound = shift;
	my $sum = shift;
	my $num = shift;
	my @output = ();
	#adds points to force convenience
	for my $i (0..$dim - 1){
		my @vec = (0) x ($dim);
		addToIndex(\@vec, $i, int(rand($cbound - 1) + 1));
		push(@output, \@vec);
	}
	#adds other point
	for my $i (0..$num - 1){
		my $total = int(rand($sum));
		my @rand = ();
		for my $j (0..$dim - 1){
			push(@rand, int(rand($total + 1)));
		}
		if (sumArray(\@rand) == 0){
			next;
		}
		my @sorted = sort {$a <=> $b} @rand;
		my @result = ($sorted[0]);
		for my $j (1..$dim - 2){
			push(@result, $sorted[$j] - $sorted[$j - 1]);
		}
		push(@result, $total - $sorted[$dim - 2]);
		push(@output, \@result);
	}

	#removes points that have the same projection
	#keeps a random point
	my @final = ();
	my @proj = map(hProjection($_, 1), @output);
	my %hash;
	for my $i (0.. scalar(@proj) - 1){
		my $str = "@{$proj[$i]}";
		if (not $hash{$str}){
			$hash{$str} = 1;
			push(@final, $output[$i]);
		}
	}

	return \@final;
}
#usage: boundaryRND($dim, $cbound, $sum, $num)
#generates a random RND
#the vertices of excess 0 are up to the size of CBound
#randomly chooses a number beween 2 and n - 1
#randomly chooses those guys to be a sum between 0 and sum
sub boundaryRND{
	my $dim = shift;
	my $cbound = shift;
	my $sum = shift;
	my $num = shift;
	my @output = ();
	#adds points to force convenience
	for my $i (0..$dim - 1){
		my @vec = (0) x ($dim);
		addToIndex(\@vec, $i, int(rand($cbound - 1) + 1));
		push(@output, \@vec);
	}
	#generate list of subsets

	my @list_of_subsets = ();
	for my $i (2..$dim){
		my @subs = subsets([0.. $dim - 1], $i);
		push(@list_of_subsets, \@subs);
	}
	#adds other point
	for my $i (0..$num - 1){
		#chooses the random subset to be non-vanishing on
		my $numnon0 = int(rand($dim - 2) + 2);
		my @goodsubs = @{$list_of_subsets[$numnon0 - 2]};
		my @non_vanishing = @{$goodsubs[int(rand(scalar(@goodsubs)))]};
		#generates the points
		my $total = int(rand($sum));
		my @rand = ();
		for my $j (0..$numnon0 - 1){
			push(@rand, int(rand($total + 1)));
		}
		if (sumArray(\@rand) == 0){
			next;
		}
		my @sorted = sort {$a <=> $b} @rand;
		my @result = ($sorted[0]);
		for my $j (1..$numnon0 - 2){
			push(@result, $sorted[$j] - $sorted[$j - 1]);
		}
		push(@result, $total - $sorted[$numnon0 - 2]);

		#now inserts the non-zero coords into the final point
		my @final = ();
		my $index = 0;
		for my $i (0..$dim - 1){
			if (($index < $numnon0) and ($i == $non_vanishing[$index])){
				push(@final, $result[$index]);
				$index ++;
			}
			else{
				push(@final, 0);
			}
		}
		push(@output, \@final);
	}

	#pArrArr(\@output);
	#removes points that have the same projection
	#keeps a random point
	my @last = ();
	my @proj = map(hProjection($_, 1), @output);
	my %hash;
	for my $i (0.. scalar(@proj) - 1){
		my $str = "@{$proj[$i]}";
		if (not $hash{$str}){
			$hash{$str} = 1;
			push(@last, $output[$i]);
		}
	}

	return \@last;


}



#usage: toProjective(aref)
#adds a 1 to the end of the array
#interpret as projectivizing the point
sub toProjective{
	my $aref = shift;
	my @array = @{$aref};
	push(@array, 1);
	return \@array;
}


#usage: toProjectiveArray($AoA)
#takes an arref of arrefs
#interprets as an array of points
#projectivizes them by adding 1 to end of each coord
sub toProjectiveArray{
	my $aref = shift;
	my @array = @{$aref};
	my @proj = map(toProjective($_), @array);
	return \@proj;
}


#usage: shiftToInfinity($AoA)
#inteprets each array in the AoA as a point in projective
#does projective linear transformation, shifts origin to infinity
#must already be projectivized!
#output is still projectivized
sub shiftToInfinity{
	my @points = @{shift @_};
	#creates the projective linear transformation 
	my $dim = scalar(@{$points[0]});
	my @mat = ();
	for my $j (0.. $dim - 3){
		my @row = (0) x ($dim);
		$row[$j] = 1;
		push(@mat, \@row);
	}
	my @v = (1) x ($dim);
	$v[$dim - 1] = -1;
	push(@mat, \@v);
	my @v2 = (1) x ($dim);
	$v2[$dim - 1] = 0;
	push(@mat, \@v2);
	my $trans = pdl(\@mat);

	#applies the transformation
	my @output = ();
	for my $i (0..scalar(@points) - 1){
		my $pvecT = pdl $points[$i];
		my $pvec = pdl $pvecT->transpose;
		my $res = $trans x $pvec;
		my @result = $res->list;
		push(@output, \@result);
		
	}
	return \@output;
}
#usage: deProjective(AoA)
#takes an array of arrays, scales so that the last coordinant is 1
#the removes the last coordinant
sub deProjective{
	my @points = @{shift @_};
	my $dim = scalar(@{$points[0]});
	my @output = ();
	for my $i (0.. scalar(@points) - 1){
		my @vec = ();
		for my $j (0..$dim - 2){
			$vec[$j] = new Rational ($points[$i]->[$j])/($points[$i]->[$dim - 1]);
		}
		push(@output, \@vec);
	}
	return \@output;
}

#usage: toStandard(AoA)
#interprets the arrays as points on the simplex conv(0, e_1, \dotsc, e_n)
#returns an array of arrays, in the same order
#corresponding points on the simplex conv(e_0, e_1, \dotsc, e_n)
sub toStandard{
	my @points = @{shift @_};
	my @output = ();
	for my $i (0..scalar(@points) - 1){
		my @point = @{$points[$i]};
		my @newpoint = (1 - sumArray(\@point));
		push(@point, @newpoint);
		push(@output, \@point);
	}
	return \@output;
}


#usage: diagramToSubdiv(AoA)
#treats the array of arrays as an array of points
#all points should have the same dimension, should include the standard basis vectors (must be convenient)
sub diagramToSubdiv{
	my $diagram = shift;
	my $proj = toProjectiveArray($diagram);
	my $shifted = shiftToInfinity($proj);
	my @new = @{deProjective($shifted)};
	#points are now in the form (points in simplex in R^d, weight)
	my @weighvec = ();
	for my $i (0.. scalar(@new) - 1){
		$weighvec[$i] = pop(@{$new[$i]});
	}
	my $coords = toStandard(\@new);
	my @baryCoords = map(toBarycentricCoords($_), @{$coords});


	my $dim = scalar(scalar(@{$diagram->[0]}));
	my $weightsRef = new Vector<Rational>(\@weighvec);
 	my $baryMat=new Matrix<Rational>(\@baryCoords);
    my $subdiv = new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat, 
    	INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
    #checks if it is not a triangulation
    if ($subdiv->DIM == $dim - 1){
    	return $subdiv;
    }
    return 1;

}

#usage: nonSimpDiagramToSubdiv(AoA)
#treats the array of arrays as an array of points
#all points should have the same dimension, should include the standard basis vectors (must be convenient)
#does not check if the subdivision is a triangulation
sub nonSimpDiagramToSubdiv{
	my $diagram = shift;
	my $proj = toProjectiveArray($diagram);
	my $shifted = shiftToInfinity($proj);
	my @new = @{deProjective($shifted)};
	#points are now in the form (points in simplex in R^d, weight)
	my @weighvec = ();
	for my $i (0.. scalar(@new) - 1){
		$weighvec[$i] = pop(@{$new[$i]});
	}
	my $coords = toStandard(\@new);
	my @baryCoords = map(toBarycentricCoords($_), @{$coords});


	my $dim = scalar(scalar(@{$diagram->[0]}));
	my $weightsRef = new Vector<Rational>(\@weighvec);
 	my $baryMat=new Matrix<Rational>(\@baryCoords);
    my $subdiv = new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat, 
    	INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
    return $subdiv;

}

#usage: isLatticePyramid($diagram, facet)
#checks if the facet is a lattice pyramid
#the facet should be a facet of the corresponding subdivision, although the code doescn't check for that
#returns 1 if it is a lattice pyramid, 0 otherwise 
#the diagram must be reduced
sub isLatticePyramid{
	my $diagram = shift;
	my @facet = @{shift @_};
	my $n = scalar(@facet);
	for my $i (0..$n - 1){
		my $sum = 0;
		for my $j (0..$n-1){
			$sum += ($diagram->[$facet[$j]])->[$i];
		}
		if ($sum == 1){
			return 1;
		}
	}
	return 0;
}

#usage: returnQ($diagram, $subdivision, facet)
#input the diagram as an AoA
#input the associated subdivision
#input a facet of the subdivision - input as numbers between 0 and n
#computes where (1,1,,1) lands
#returns an array with Q
sub returnQ{
	my $diagram = shift;
	my $subdiv = shift;
	my $facet = shift;
	my $dim = scalar(@{$facet}) - 1;
	#creates AoA of the coordinants of of P
	my @coords = ();
	for my $i (0..$dim){
		push(@coords, $diagram->[$facet->[$i]]);
	}
	#now we find where (1,1,..,1) lands
	#to do this, solve Ax = b, b = (1,1..,1), A = matrix whose rows are the coordinant vectors of the face
	#The entries that are integers is what we care about
	#first creates (1,1,,1)
	my @row = (1) x ($dim + 1);
	my $r = pdl[\@row];
	my $target = $r->transpose;
	#now creates the matrix of the coords
	my $tpose = pdl[\@coords];
	my $mat = $tpose->transpose;
	my $inv = inv($mat);
	my $res = $inv x $target;
	#finds the non-integer, finds Q
	#due to some stupid machine precision stuff, checks if it is within 10^{-8}
	my @Q = ();
	my @res = $res->list;
	for my $j (0..$dim){
		if (abs($res[$j] - round($res[$j])) > 0.00000001){
			push(@Q, $facet->[$j]);
		}
	}
	return \@Q;
}


#usage: checkFacet($diagram, $subdivision, facet)
#input the diagram as an AoA
#input the associated subdivision
#input a facet of the subdivision - input as numbers between 0 and n
#computes where (1,1,,1) lands
#computes relative local $h$
#returns an array with relative local h and the codimension of the carrier
#Must be reduced!
sub checkFacet{
	my $diagram = shift;
	my $subdiv = shift;
	my $facet = shift;
	my $dim = scalar(@{$facet}) - 1;
	#creates AoA of the coordinants of of P
	my @coords = ();
	for my $i (0..$dim){
		push(@coords, $diagram->[$facet->[$i]]);
	}
	#now we find where (1,1,..,1) lands
	#to do this, solve Ax = b, b = (1,1..,1), A = matrix whose rows are the coordinant vectors of the face
	#The entries that are integers is what we care about
	#first creates (1,1,,1)
	my @row = (1) x ($dim + 1);
	my $r = pdl[\@row];
	my $target = $r->transpose;
	#now creates the matrix of the coords
	my $tpose = pdl[\@coords];
	my $mat = $tpose->transpose;
	my $inv = inv($mat);
	my $res = $inv x $target;
	#finds the non-zero entries, finds Q
	my @Q = ();
	my @res = $res->list;
	for my $j (0..$dim){
		if ((abs($res[$j] - round($res[$j])) > 0.00000001)){
			push(@Q, $facet->[$j]);
		}
	}
	#pArr(\@Q);
	#print "Codimension is ", ($dim + 1 - ($dim + 1 - scalar(@{carrier($subdiv, \@Q)}))), "\n";
	return (relativeLocalH($subdiv, \@Q), scalar(@{carrier($subdiv, \@Q)}));
}






#usage: gatherCDData($dim, iterations)
#generates a bunch of random uniformRND($dim, 500, 10, 20)
#find non-pyramidal facets
#checks those facets
sub gatherCDData{
	my $dim = shift;
	my $iter = shift;
	my @codim = (0) x ($dim + 1);
	my @localh = ();
	for my $i (0..$iter){
		my $diagram = uniformRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @npfacets = @{returnNonPyramidalFaces($subdiv)};
		for my $facet (@npfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my @res = checkFacet($diagram, $subdiv, \@facet);
			$codim[$res[1]] += 1;
			if (sumArray($res[0]) == 0){
				pArrArr($diagram);
			}
			if ($res[1] > 2){
				push(@localh, $res[0]);
			}
		}
	}
	pArr(\@codim);
	return \@localh
}

#usage: gatherCDDataSum($dim, iterations)
#generates a bunch of random sumRND($dim, 500, 30, 20)
#find non-pyramidal facets
#checks those facets
sub gatherCDDataSum{
	my $dim = shift;
	my $iter = shift;
	my $none = 0;
	my $nottry = 0;
	my @codim = (0) x ($dim + 1);
	my @localh = ();
	for my $i (0..$iter){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			$nottry++;
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @npfacets = @{returnNonPyramidalFaces($subdiv)};
		if (scalar(@npfacets) == 0){
			$none++;
		}
		for my $facet (@npfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			$codim[$cdim] += 1;
			if ($cdim > 2){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					pArrArr($diagram);
				}
				push(@localh, $lh);
			}
		}
	}
	print "Number with no non-pyramidal facets is ", $none, "\n";
	print "Number that are not triangulations is ". $nottry, "\n";
	pArr(\@codim);
	return \@localh
}


#usage: multiplicity($aref, $aref)
#computes the multiplicity of a pair of integer vectors
#i.e. computes the index of the lattice generated by the vectors in the group of all lattice points 
#in the vector space spanned by the vectors
#does this by taking the gcd of the determinents of the 2x2 minors
sub multiplicity{
	my @v1 = @{shift @_};
	my @v2 = @{shift @_};
	my @pairs = subsets([0..scalar(@v1)-1], 2);
	my $gcd = new Integer abs($v1[0]*$v2[1] - $v2[0]*$v1[1]);
	for my $sub(@pairs){
		my $det = abs($v1[$sub->[0]]*$v2[$sub->[1]] - $v2[$sub->[0]]*$v1[$sub->[1]]);
		my $toint = new Integer($det);
		$gcd = gcd($gcd, $toint);
		if ($gcd == 1){
			last;
		}
	}
	return $gcd;
}

#usage: removeRedundant(diagram, associated subdivision)
#takes a diagram and the resuling subdivision, remove the points that don't contribute to the subdivision
#returns the reduced diagram
sub removeRedundant{
	my @diagram = @{shift @_};
	my $subdiv = shift;
	my @good = @{$subdiv->VERTEX_INDICES};
	my @relevant_faces = ();
	for my $index (@good){
		push(@relevant_faces, $diagram[$index]);
	}

	return \@relevant_faces;
}

#usage: makePrimitive(array of integers)
#array must be all integral
#divides through by gcd of all entries
#there are some issues with gcd and mod and data type, polymake has a built in gcd function
sub makePrimitive{
	my @vec = @{shift @_};
#	#checks if integral
#	my $int = 1;
#	for my $i (0.. scalar(@vec) - 1){
#		if ($vec[$i] != ceil($vec[$i])){
#			$int = 0;
#			last;
#		}
#	}
#	if ($int == 0){
#		my $num = 1;
#		for my $i (0..scalar(@vec) - 1){
#			$num = $num * denominator($vec[$i]);
#		}
#		@vec = map(($_) * $num, @vec);
#	}
	my $gcd = gcd($vec[0], $vec[1]);
	for my $i (2..scalar(@vec) - 1){
		$gcd = gcd($gcd, abs($vec[$i]));
		if ($gcd == 1){
			last;
		}
	}
	my @result = map(new Rational($_/$gcd), @vec);
	return \@result;
}


#usage(diagram, aref of facets)
#for each facet, returns the primitive vector in the dual cone
#must have no redundant points in the diagram
sub primitiveDualVector{
	my @diagram = @{shift @_};
	my @flist = @{shift @_};
	#converts to homogeneous coords by adding 1 to the start of everything
	my @points = ();
	for my $i (0..scalar(@diagram) - 1){
		my @guy = (1);
		push(@guy, @{$diagram[$i]});
		push(@points, \@guy);
	}
	my $p = new Polytope(POINTS=>\@points);
	my $facets = $p->FACETS;
	#finds the indices of the facets I care about
	my @labels = ();
	my @facet_labels = @{$p->VERTICES_IN_FACETS};
	my @AoAfacet_labels = map(vectorToArray($_), @facet_labels);
	for my $face (@flist){
		for my $i (0..scalar(@AoAfacet_labels) - 1){
			if (entrywiseEquality($face, $AoAfacet_labels[$i])){
				push(@labels, $i);
			}
		}
	}
	if(scalar(@labels) != scalar(@flist)){
		print "Not simplicial";
		return 1;
	}
	#finds the normal vector to each of the good facets
	my @normals = ();
	for my $i (0..scalar(@flist) - 1){
		my @norm = @{$facets->[$labels[$i]]};
		shift(@norm);
		push(@normals, (\@norm));
	}
	return \@normals;
}

#usage: dot of two arrays
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

#usage: LoeserConditionNPyramidal($diagram, $subdiv)
#takes a diagram and an associated subdivisions
#find the Non pyramidal faces

sub LoeserConditionNPyramidal{
	my $diagram = shift;
	my $subdiv = shift;
	my $reduced = removeRedundant($diagram, $subdiv);
	my @npfacets = map(vectorToArray($_), @{returnNonPyramidalFaces($subdiv)});
	my @allfacets = map(vectorToArray($_), @{$subdiv->FACETS});
	my @npdualvecs = @{primitiveDualVector($diagram, \@npfacets)};
	my @dualvecs = @{primitiveDualVector($diagram, \@allfacets)};

	for my $i (0..scalar(@npfacets) - 1){
		pArr $npfacets[$i];
		my $N = dot($npdualvecs[$i], $reduced->[$npfacets[$i]->[0]]);
		my $nu = sumArray($npdualvecs[$i]);
		my $thing = $nu/$N;

		for my $j (0..scalar(@allfacets) - 1){
			my $lc = List::Compare->new($allfacets[$j], $npfacets[$i]);
			if ((scalar($lc->get_intersection) > 0) and (not entrywiseEquality($allfacets[$j], $npfacets[$i]))){
				my $lambda = sumArray($allfacets[$j]) - $thing * dot($allfacets[$j], $reduced->[$allfacets[$j]->[0]]);
				my $beta = multiplicity($npdualvecs[$i], $dualvecs[$j]);
				if (denominator($lambda/$beta) == 1){
					print scalar($lc->get_intersection);
				}
				#print "Currently on facet:";
				#pArr $allfacets[$j];
				#print "Lambda is ", $lambda, " Beta is ", $beta, " so mu is ", $lambda/$beta, "\n";
			}
		}
	}

}

#checks the "topological pyramid implies lattice pyramids" conjecture

sub checkAllFaces{
	my $dim = shift;
	my $iter = shift;
	my $none = 0;
	my $nottry = 0;
	my @codim = (0) x ($dim + 1);
	my @localh = ();
	for my $i (0..$iter){
		my $diagram = uniformRND($dim, 100, 10, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			$nottry++;
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @allfacets = @{$subdiv->FACETS};
		if (scalar(@allfacets) == 1){
			$trivial++;
		}
		for my $facet (@allfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			$codim[$cdim] += 1;
			if ($cdim > 2){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					print "Found one \n";
					pArr(\@facet);
					pArr($Q);
					pArrArr($diagram);
				}
				push(@localh, $lh);
			}
		}
	}
	print "Number which have a trivial subdivision is ", $none, "\n";
	print "Number that are not triangulations is ". $nottry, "\n";
	pArr(\@codim);
	return \@localh
}

#usage: returnNLPyramids($diagram, $subdiv)
#returns all the faces that are not lattice pyramids
sub returnNLPyramids{
	my $diagram = shift;
	my $subdiv = shift;
	my $nfacets = $subdiv->N_FACETS;
	my @NLs = ();
	for my $i (0..$nfacets - 1){
		my @facet = @{$subdiv->FACETS->[$i]};
		if (not isLatticePyramid($diagram, \@facet)){
			push(@NLs, \@facet);
		}
	}
	return \@NLs;
}

#usage: returnNLPyramids($diagram, $subdiv)
#returns an array containing all pyramidal facets that are not lattice pyramids
#does this by itterating over the facets, finding all facets that aren't lattice pyramids and aren't non-pyramidal
#diagram must be reduced
sub returnNLPPyramids{
	my $diagram = shift;
	my $subdiv = shift;
	my $nfacets = $subdiv->N_FACETS;
	my @NLs = ();
	for my $i (0..$nfacets - 1){
		my @facet = @{$subdiv->FACETS->[$i]};
		if ((not isLatticePyramid($diagram, \@facet)) and (not checkMaximalFace($subdiv, \@facet))){
			push(@NLs, \@facet);
		}
	}
	return \@NLs;
}

#usage: nonLatticePyramid($dim, iter)
#generates a random subdivision
#itterates over the faces that aren't lattice pyramids
#divides into non-pyramidal faces and NL pyramids
#computes Q for the NL pyramids, returns an array 
sub nonLatticePyramid{
	my $dim = shift;
	my $iter = shift;
	my @dimQ = (0) x ($dim);
	my @codim = (0) x ($dim);
	my $numFacets = 0;

	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 1000, 10, 20);

		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @NLs = @{returnNLPPyramids($diagram, $subdiv)};
		$numFacets += scalar(@NLs);
		for my $face (@NLs){
			my $Q = returnQ($diagram, $subdiv, $face);
			#pArr $Q;
			if (sumArray(relativeLocalH($subdiv, $Q)) == 0){
				pArrArr $diagram;
			}
			#pArrArr $diagram;
			$dimQ[scalar(@{$Q})] += 1;
			$codim[scalar(@{carrier($subdiv, $Q)})] += 1;
		}
	}
	print "Found a total of ", $numFacets, " Non-lattice pyramids, and their dimensions and carrier codims were: \n";
	pArr (\@dimQ);
	pArr (\@codim);

}

#usage: checkAllCandidatesCounterexamples($dim $iter)
#generates a bunch of random subdivisons
#looks at both non-pyramidal faces and non-lattice pyramids
sub checkAllCandidatesCounterexamples{
	my $dim = shift;
	my $iter = shift;
	my $none = 0;
	my $nottry = 0;
	my @localh = ();
	for my $i (0..$iter){
		my $diagram = sumRND($dim, 10000, 20, 50);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			$nottry++;
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @nLfacets = @{returnNLPyramids($diagram, $subdiv)};
		if (scalar(@nLfacets) == 0){
			$none++;
		}
		for my $facet (@nLfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			if ((checkMaximalFace($subdiv, $Q) and $cdim > 2) or (not checkMaximalFace($subdiv, $Q) and $cdim > 0)){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					pArrArr($diagram);
				}
				push(@localh, $lh);
			}
		}
	}
	print "Number with no non-lattice pyramid facets is ", $none, "\n";
	print "Number that are not triangulations is ". $nottry, "\n";
	return \@localh

}

#usage: computeNLPyramidStats($dim, $iter)
#computes a bunch of sumRND diagrams
#finds the pyramid faces that are not lattice pyramids
#computes relative local h relative to faces contained in them
#prints the result
sub computeNLPyramidStats{
	my $dim = shift;
	my $iter = shift;
	my @vanishing = (0) x ($dim + 1);
	my @codim = (0) x @vanishing;
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 20, 50);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @faces = @{returnNLPPyramids($diagram, $subdiv)};

		my @toconsider = ();
		for my $j (0..scalar(@faces) - 1){
			#creates array of faces, gets rid of the empty set and whole facet
			my @facet = @{$faces[$j]};
			my @faces = subarrs(@facet);
			shift(@faces);
			pop(@faces);
			push(@toconsider, @faces);
		}
		my @flist = @{removeDuplicates(\@toconsider)};
		for my $face (@flist){
			$codim[scalar(@{carrier($subdiv, $face)})] ++;
			if (sumArray(relativeLocalH($subdiv, $face)) == 0){
				$vanishing[scalar(@{carrier($subdiv, $face)})] ++;
			}
		}
	}
	pArr(\@vanishing);
	pArr(\@codim);
}

#usage:pyramidOverFace($subdiv, $facet, $face)
#checks if the facet is a pyramid over the face
#face must be contained in the facet
#returns 1 if it is a pyramid over the face, 0 if not
sub pyramidOverFace{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my $face = shift;
	my @carrier = @{carrier($subdiv, $face)};
	if (scalar(@carrier) == 0){
		return 0;
	}
	for my $i (@carrier){
		my $num = 0;
		for my $j (@facet){
			if ($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$j]]->[$i] !=0){
				$num ++;
				if ($num == 2){
					last;
				}
			}
		}
		if ($num != 2){
			return 1;
		}
	}
	return 0;

}


#usage: checkRelativeVanishingNotPyramidOver(array of subdivisions, all of the same dim)
#prints two arrays
#for each complex, looks at a random facet. Finds all subfaces such that the facet is not a pyramid over that face
#computes relative local h
sub checkRelativeVanishingNotPyramidOver{
	my $list = shift;
	my @list = @{$list};
	my $size = $list[0]->DIM + 1;
	my @v = (0) x ($size);
	my @t = (0) x @v;
	for my $i (0..scalar(@list) - 1){
		if ($list[$i]->N_FACETS > 5){
			my $facet = $list[$i]->FACETS->[3];
			my @facet2 = @{$facet};
			my @candidates = subarrs(@facet2);
			shift(@candidates);
			pop(@candidates);
			my @good = ();
			for my $face (@candidates){
				if (not pyramidOverFace($list[$i], \@facet2, $face)){
					push(@good, $face);
				}
			}
			for my $face (@good){
				$t[scalar(@{$face})] ++;
				if (sumArray(relativeLocalH($list[$i], $face)) == 0){
					$v[scalar(@{$face})] ++;
				}
			}
		}
	}
	print "Total number of vanishing: ";
	pArr(\@v);
	print "Total number: ";
	pArr(\@t);
}

#usage: gatherCDDataBoundary($dim, iterations)
#generates a bunch of random sumRND($dim, 500, 30, 20)
#find non-pyramidal facets
#checks those facets
sub gatherCDDataBoundary{
	my $dim = shift;
	my $iter = shift;
	my $none = 0;
	my $nottry = 0;
	my @codim = (0) x ($dim + 1);
	my @localh = ();
	for my $i (0..$iter){
		my $diagram = boundaryRND($dim, 10000, 20, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			$nottry++;
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @npfacets = @{returnNonPyramidalFaces($subdiv)};
		if (scalar(@npfacets) == 0){
			$none++;
		}
		for my $facet (@npfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			$codim[$cdim] += 1;
			if ($cdim > 2){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					pArrArr($diagram);
				}
				push(@localh, $lh);
			}
		}
	}
	print "Number with no non-pyramidal facets is ", $none, "\n";
	print "Number that are not triangulations is ". $nottry, "\n";
	pArr(\@codim);
	return \@localh
}
#usage: diagramToString($diagram)
#turns the diagram into a string
#puts an X between different vertices
sub diagramToString{
	my @diagram = @{shift @_};
	my $string = "@{$diagram[0]}";
	for my $i (1..scalar(@diagram) - 1){
		$string = $string . "X" . "@{$diagram[$i]}";
	}
	return $string;
}

#usage: stringToDiagram(string, $dim)
#takes a string output by a diagram, turns it into a diagram
sub stringToDiagram{
	my $string = shift;
	my @diagram = ();
	my @points = split(/X/, $string);
	for my $point (@points){
		my @array = split(/ /, $point);
		push(@diagram, \@array);
	}
	return \@diagram;

}



#usage: generateDiagrams($dim, $iter)
#generates a bunch of diagrams, returns the subdivisions and the diagrams, also checks if they give counterexamples
sub generateDiagrams{
	my $dim = shift;
	my $iter = shift;
	my @diagrams = ();
	my @subdivs = ();
	my $none = 0;
	my $nottry = 0;
	my @codim = (0) x ($dim + 1);
	my $l10 = 0;
	my $l20 = 0;
	for my $i (0..$iter){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			$nottry++;
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		push(@diagrams, $diagram);
		push(@subdivs, $subdiv);
		my @npfacets = @{returnNonPyramidalFaces($subdiv)};
		if (scalar(@npfacets) == 0){
			$none++;
		}
		for my $facet (@npfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			$codim[$cdim] += 1;
			if ($cdim > 2){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					pArrArr($diagram);
				}
				if ($lh->[1] == 0){
					$l10 ++;
				}
				if ($lh->[2] == 0){
					$l20++;
				}
			}
		}
	}
	print "Number with no non-pyramidal facets is ", $none, "\n";
	print "Number that are not triangulations is ". $nottry, "\n";
	pArr(\@codim);
	print "Number with l1 and l2 0 is ", $l10, " ", $l20, "\n";
	
	return (\@subdivs, \@diagrams);

}

#usage: findEmptySetCase($dim, $iter)
#searches for cases when Q is the emptyset
#also checks if they give counterexamples
sub findEmptySetCase{
	my $dim = shift;
	my $iter = shift;
	my @diagrams = ();
	my @subdivs = ();
	for my $i (0..$iter){
		my $diagram = uniformRND($dim, 10000, 10, 4);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @npfacets = @{returnNonPyramidalFaces($subdiv)};

		for my $facet (@npfacets){
			#this line is necessary to convert from vector to aref
			my @facet = @{$facet};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			if (scalar(@{$Q}) == 0){
				push(@diagrams, $diagram);
				push(@subdivs, $subdiv);
				last;
			}
			my $cdim = scalar(@{carrier($subdiv, $Q)});
			if ($cdim > 2){
				my $lh = relativeLocalH($subdiv, $Q);
				if (sumArray($lh) == 0){
					pArrArr($diagram);
				}

			}
		}
	}	
	return (\@subdivs, \@diagrams);
}

#usage: findEmptySets($diagram, $subdiv)
#takes a subdivision and a diagram, returns the non-pyramidal faces
#for which Q = emptyset
sub findEmptySets{
	my $diagram = shift;
	my $subdiv = shift;

	my @facets = @{returnNonPyramidalFaces($subdiv)};
	my @giveempty = ();
	for my $f (@facets){
		my @facet = @{$f};
		if (scalar(@{returnQ($diagram, $subdiv, \@facet)}) == 0){
			push(@giveempty, $f);
		}
	}
	return \@giveempty;
}

#usage: typeGraph($subdiv, $aref of vertices)
#interprets the combinatorial type of the facet as the incidence matrix of a bipartite graph
#generates the bipartite graph
#the isomorphism classes of these bipartite graphs determine the combinatorial type up to an isomorphism 
#that does not interchange the color classes
sub typeGraph{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my $n = scalar(@facet);
	my @edges = ();
	for my $i (0..$n - 1){
		my $coords = $subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$facet[$i]]];
		for my $j (0.. $n - 1){
			if ($coords->[$j] > 0){
				push(@edges, [$i, $j + $n]);
			}
		}
	}
	my $graph = new topaz::SimplicialComplex(INPUT_FACES=>\@edges);
	return $graph;
}


#usage: skelToGraph(1-dimensional simplicial complex)
#returns a graph of that complex
sub skelToGraph{
	my $simp = shift;
	my @edges = map(vectorToArray($_), @{$simp->FACETS});
	return graph_from_edges(\@edges);
}


#usage: findCandidatePole(diagram, facet)
#returns the candidate pole associated to that facet
#diagram must be reduced or answer will be wrong!
sub findCandidatePole{

}

#usage: topologicalZetaFunction($diagram, $subdiv)
#computes the topological zeta function
sub topologicalZetaFunction{

}
#usage: gatherCombTypeData(dim, iter)
#generates a bunch of subdivisions
#for each subdivision, find the non-pyramidal faces
#For each non-pyramidal face, computes Q
#stores the combinatorial type of the non-pyramidal facet in graph form in the proper files
#returns an array of AoAs
#Each array will be determined the number of vertices where Q lands
#The array with in the array will be by excess
#Only stores if the codimension is greater than 2
#returns an array
sub gatherCombTypeData{
	my $dim = shift;
	my $iter = shift;
	#generates the results table
	my @results = ();
	for my $i (0..$dim - 3){
		push(@results, []);
	}
	for my $j (0..$dim - 3){
		my @carrier_dim = ([]) x ($dim - 2 - $j);
		push(@{$results[$j]}, @carrier_dim);
	}
	#generates the subdivisions
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		my @faces = @{returnNonPyramidalFaces($subdiv)};
		if (scalar(@faces) == 0){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		for my $f (@faces){
			my @facet = @{$f};
			my $Q = returnQ($diagram, $subdiv, \@facet);
			if (scalar(@{carrier($subdiv, $Q)} < 3)){
				next;
			}
			my $g = typeGraph($subdiv, \@facet);
			my $vert = scalar(@{$Q});
			my $excess = excess($subdiv, $Q);
			push(@{$results[$vert]->[$excess]}, $g);
		}

	}
	return @results;
}


#usage: vanishingTypeGraph($subdiv)
#finds the non-pyramidal faces
#computes, up to carrier codimension 2, relative local h relative to each
#if relative local h vanishes, then puts the type graph in the appropriate place
#same return type as gatherCombTypeData
sub vanishingTypeGraph{
	my $subdiv = shift;
	#generates the results table
	my @results = ();
	my $dim = $subdiv->DIM;
	for my $i (0..$dim - 3){
		push(@results, []);
	}
	for my $j (0..$dim - 3){
		my @carrier_dim = ([]) x ($dim - 2 - $j);
		push(@{$results[$j]}, @carrier_dim);
	}
	my @faces = @{returnNonPyramidalFaces($subdiv)};
	for my $f (@faces){
		my @facet = @{$f};
		my $g = typeGraph($subdiv, \@facet);
		my @tolook = subarrs(@facet);
		shift(@tolook);
		pop(@tolook);
		for my $face (@tolook){
			if(scalar(@{carrier($subdiv, $face)}) < 3 ){
				next;
			}
			if (sumArray(relativeLocalH($subdiv, $face)) == 0){
				push(@{$results[scalar(@{$face})]->[excess($subdiv, $face)]}, $g);
			}
		}
	}
	return @results;
}

#usage: removeIsomorphic(list of simplicial complexes)
#generates a list of the simplicial complexes up to isomorphism
#it would be more efficient to do this using a canonical labeling
sub removeIsomorphic{
	my @list = @{shift @_};
	my @nodupes = ();
	my $new = 1;
	for my $i (0..scalar(@list) - 1){
		for my $j (0..scalar(@nodupes) - 1){
			if (isomorphic($list[$i], $nodupes[$j])){
				$new = 0;
				last;
			}
		}
		if ($new == 1){
			push(@nodupes, $list[$i]);
		}
		$new = 1;
	}
	return \@nodupes;
}

#usage: compareLists(list of simps, list of simps)
#prints if there are any two that are isomorphic
#to be efficient, each list should have no duplicates
sub compareLists{
	my $list1 = shift;
	my $list2 = shift;
	for my $i (0..scalar(@{$list1}) - 1){
		for my $j (0..scalar(@{$list2}) - 1){
			if (isomorphic($list1->[$i], $list2->[$j])){
				print "$i and $j are isomorphic \n";
			}
		}
	}
}

#usage: checkTypeIsomorphism($aref, $aref)
#the $arefs should be of the type given by vanishingTypeGraph and gatherCombTypeData
#need to be the same dimension!
#unfinishes
sub checkTypeIsomorphism{
	my @res1 = @{shift @_};
	my @res2 = @{shift @_};

}

#usage: checkIntConjecture($subdiv, $facet, face)
#assumes relative local h relative to face is 0
#only assumes the case of \ell_1 for the conjecture
sub checkIntConjecture{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my @face = @{shift @_};
	my $lc = List::Compare->new(\@facet, \@face);
	my @comp = $lc->get_unique;
	if (scalar(@comp) < 4){
		return 0;
	}
	for my $k (2..int(scalar(@comp)/2)){
		my @divisions = subsets(\@comp, $k);
		for my $split (@divisions){
			if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
				next;
			}
			my $list = List::Compare->new(\@comp, $split);
			my @other = $list->get_unique;
			if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
				print "Found one! \n";
				printSubdiv($subdiv); 
			}
			#find the most efficient way to check if the complement has excess 0
			#it is probably faster to use list compare
		}
	}
}

#usage: checkIntConjectureAll($subdiv)
#find every (facet, face) pair for which relative local h vanishes (not just npyramidal)
#checks the conjecture in that case
#only checks if it is a pyramid over the face
sub checkIntConjectureAll{
	my $subdiv = shift;
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @faces = subsets(vectorToArray($facet));
		for my $face (@faces){
			if (scalar(@{carrier($subdiv, $face)}) < 3){
				next;
			}
			if (pyramidOverFace($subdiv, $facet, $face)){
				next;
			}
			if (sumArray(relativeLocalH($subdiv, $face)) == 0){
				checkIntConjecture($subdiv, $facet, $face);
			}
		}
	}
}

#usage: checkIntConjectureNP($subdiv)
#find every (facet, face) pair for which relative local h vanishes 
#checks the conjecture for all non-pyramidal facets
sub checkIntConjectureNP{
	my $subdiv = shift;
	my @facets = @{returnNonPyramidalFaces($subdiv)};
	for my $facet (@facets){
		my @faces = subsets(vectorToArray($facet));
		for my $face (@faces){
			if (scalar(@{carrier($subdiv, $face)}) < 3){
				next;
			}
			if (sumArray(relativeLocalH($subdiv, $face)) == 0){
				checkIntConjecture($subdiv, $facet, $face);
			}
		}
	}
}


#usage: checkIntConjectureRandList($list of subdivs)
#checks all relative vanishing pairs for 3 basically random facets
#checks the conjecture for all non-pyramidal facets
sub checkIntConjectureRandList{
	my @list = @{shift @_};
	for my $i (0..scalar(@list) - 1){
		if ($list[$i]->N_FACETS < 7){
			next;
		}
		my @facets = ($list[$i]->FACETS->[4], $list[$i]->FACETS->[5], $list[$i]->FACETS->[6]);
		for my $facet (@facets){
			my @faces = subsets(vectorToArray($facet));
			for my $face (@faces){
				if (scalar(@{carrier($list[$i], $face)}) < 3){
					next;
				}
				if (pyramidOverFace($list[$i], $facet, $face)){
					next;
				}
				if (sumArray(relativeLocalH($list[$i], $face)) == 0){
					checkIntConjecture($list[$i], $facet, $face);
				}
			}
		}
	}
}

#usage: numberDecomposition($subdiv, $facet, $face)
#computes the number of decompositions
sub numberDecomposition{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my @face = @{shift @_};
	my $lc = List::Compare->new(\@facet, \@face);
	my @comp = $lc->get_unique;
	if (scalar(@comp) < 4){
		return 0;
	}
	for my $k (1..int(scalar(@comp)/2)){
		my @divisions = subsets(\@comp, $k);
		for my $split (@divisions){
			if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
				next;
			}
			my $list = List::Compare->new(\@comp, $split);
			my @other = $list->get_unique;
			if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
				pArr($split);
				pArr(\@other);
			}
		}
	}
}

#usage: numberDecomposition($subdiv, $face)
#computes the number of decompositions, for all facets containing the face
sub numberDecompositionFacets{
	my $subdiv = shift;
	my @face = @{shift @_};
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		if (not is_subset(vectorToArray($facet), \@face)){
			next;
		}
		numberDecomposition($subdiv, $facet, \@face);
	}
}

#usage: jPolyCount($subdiv, face)
#computes the j-polynomial of the subdivision
#uses the definition where we count the number of splittings of facets
#inefficient in several ways, on the middle term and does not use symmetry
sub jPolyCount{
	my $subdiv = shift;
	my @face = @{shift @_};
	my @result = (0) x ($subdiv->DIM + 2 - scalar(@face));
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @facet = @{$facet};
		if (not is_subset(\@facet, \@face)){
			next;
		}
		my $lc = List::Compare->new(\@facet, \@face);
		my @comp = $lc->get_unique;
		for my $k (0..scalar(@comp)){
			my @divisions = subsets(\@comp, $k);
			for my $split (@divisions){
				if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
					next;
				}
				my $list = List::Compare->new(\@comp, $split);
				my @other = $list->get_unique;
				if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
					pArr $split;
					pArr (\@other);
					print "\n";
					$result[$k]++;
				}
			}
		}
	}
	return \@result;
}

#usage: jPolyFacets($subdiv, face)
#computes the j-polynomial of the subdivision
#uses the definition where we count the number of facets of each dimension
#again ineffeficient in many ways
sub jPolyFacets{
	my $subdiv = shift;
	my @face = @{shift @_};
	my @result = (0) x ($subdiv->DIM + 2);
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @facet = @{$facet};
		if (not is_subset(\@facet, \@face)){
			next;
		}
		if (pyramidOverFace($subdiv, $facet, \@face)){
			next;
		}
		my $lc = List::Compare->new(\@facet, \@face);
		my @comp = $lc->get_unique;
		for my $k (1..scalar(@comp) - 1){
			my @divisions = subsets(\@comp, $k);
			for my $split (@divisions){
				if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
					next;
				}
				my $list = List::Compare->new(\@comp, $split);
				my @other = $list->get_unique;
				if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
					$result[$k]++;
					last;
				}
			}
		}
	}
	return \@result;
}


#usage: jPoly($subdiv, face)
#computes the j-polynomial of the subdivision
#uses the definition where we count the number of splittings of facets
#uses symmetry
#gives an error when $subdiv is empty
sub jPoly{
	my $subdiv = shift;
	my @face = @{shift @_};
	my @result = (0) x ($subdiv->DIM + 2 - scalar(@face));
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @facet = @{$facet};
		if (not is_subset(\@facet, \@face)){
			next;
		}
		if (pyramidOverFace($subdiv, $facet, \@face)){
			next;
		}
		my $lc = List::Compare->new(\@facet, \@face);
		my @comp = $lc->get_unique;
		for my $k (0..int(scalar(@comp)/2)){
			my @divisions = subsets(\@comp, $k);
			for my $split (@divisions){
				if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
					next;
				}
				my $list = List::Compare->new(\@comp, $split);
				my @other = $list->get_unique;
				if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
					$result[$k]++;
				}
			}
		}
	}
	for my $j (0..int($subdiv->DIM  - scalar(@face))/2 ){
		$result[$subdiv->DIM + 1 - scalar(@face) - $j] = $result[$j];
	}
	return \@result;
}







#usage: admitsConicalCoarsening(subdivision, arref of facet indices)
#see 0.316 for how it works
#uses the recognition lemma
#returns (set of vertices, set of facets)
#returns the first conical coarsening it
#returns 0 if none found
sub admitsConicalCoarsening{
	my $subdiv = shift;
	my $dim = $subdiv->DIM;
	my @verts = (0..$subdiv->N_VERTICES - 1);
	my @sets = subsets(\@verts, $dim + 1);
	my @facets = @{$subdiv->FACETS};
	my $works = 1;
	for my $set (@sets){
		$works = 1;
		my @points = ();
		for my $vertex (@{$set}){
			push(@points, $subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$vertex]]);
		}
		#if the stuff is not a pyramid, then there is no conical refinement. 
		if (checkMaximalFace($subdiv, $set)){
			next;
		}
		my $poly = new Polytope<Rational>(POINTS=>\@points);
		#checks if the vertices form a simplex
		if (not ($poly->N_VERTICES == $dim + 1)){
			next;
		}
		#finds the vertices that are contained in the convex hull
		my @contained = ();
		for my $i (@verts){
			if (not separable($poly, $subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$i]])){
				push(@contained, $i);
			}
		}
		if (scalar(@contained) == $dim + 1){
			next;
		}


		#for every facet, check if the facet is contained in
		#also check if a facet violated the * condition
		my @union = ();
		my @included = ();
		for my $facet (@facets){
			my @facet = @{$facet};
			my $lc = List::Compare->new(\@facet, \@contained);
			my @int = $lc->get_intersection;
			if (scalar(@int) == 0){
				next;
			}
			if (scalar($lc->get_unique) == 0){
				push(@union, @facet);
				push(@included, \@facet);
			}
			elsif (is_subset_unsorted($set, \@int)){
				next;
			}
			else{
				$works = 0;
				last;
			}
		}
		if ($works == 0){
			next;
		}
		if (scalar(@included) == 0){
			next;
		}
		my $flist = List::Compare->new(@included);
		if (scalar($flist->get_union) != scalar(@contained)){
		}

		#checks if the refinment is conical
		#conical iff there is an original vertex that is included in every facet
		if (scalar($flist->get_intersection) > 0){
			my @int = $flist->get_intersection;
			my $final = List::Compare->new($set, \@int);
			if (scalar($final->get_intersection) > 0){
				return [$set, \@included];
			}
		}
	}
	return 0;
}

#usage: conicalCoarsening($subdiv, $set of vertices, set of facets)
#outputs as a geometric simplicial complex the results of performing the conical coarsening
#does not check that it is acutally a conical coarsening
sub conicalCoarsening{
	my $subdiv = shift;
	my @verts = @{shift @_};
	my @facets = @{shift @_};
	#gets the facets that remain
	my @allfacets = map(vectorToArray($_), @{$subdiv->FACETS});
	my @newfacets = ();
	my $good = 1;
	for my $facet (@allfacets){
		$good = 1;
		for my $bad(@facets){
			if (entrywiseEquality($facet, $bad)){
				$good = 0;
				last;
			}
		}
		if ($good == 1){
			push(@newfacets, $facet);
		}
	}
	push(@newfacets, \@verts);
	##finds the vertices in the new guy
	#my $flist = List::Compare->new(@facets);
	#my @infacets = $flist->get_union;
	#my $newlist = List::Compare->new([0..$subdiv->N_VERTICES - 1], \@infacets);
	#my @finalvertices = $newlist->get_unique;
	#@finalvertices = @{union(\@finalvertices, \@verts)};
	#makes the matrix
	#my @coords = ();
	#for my $v (@finalvertices){
	#	push(@coords, $subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$v]]);
	#}
	my @coords = ();
	for my $v (0..$subdiv->N_VERTICES - 1){
		push(@coords, $subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$v]]);
	}
	my $mat = new Matrix<Rational>(\@coords);
	return new topaz::GeometricSimplicialComplex(COORDINATES=>$mat, 
    	INPUT_FACES=>\@newfacets);
}

#usage: doAllConical($subdiv)
#repeatedly does conical coarsenings until there are no more
#returns the result
sub doAllConical{
	my $subdiv = shift;
	my $res = $subdiv;
	my $coarse = 1;

	while (1){
		$coarse = admitsConicalCoarsening($res);
		if ($coarse == 0){
			last;
		}
		$res = conicalCoarsening($res, @{$coarse});
	}
	return $res;
}

#usage: relativeInternalKSkeleton($subdiv, $face, $k)
#computes the k-dimensional complex that is the smallest that contains all k-dimensional faces
#such that \sigma(E \cup face) = 2^V
#does this by computing the \vert E \vert + k-skeleton, then checking
#doesn't work when k = 0
sub relativeInternalKSkeleton{
	my $comp = shift;
	my @E = @{shift @_};
	my $k = shift;
	my $dim = $comp->DIM;
	if (scalar(@E) + $k > $dim){
		print "Error: $k is too large";
		return 0;
	}

	#computes the \vert E \vert + k skeleton
	my $abs = new topaz::SimplicialComplex($comp);
	my $overall_k_skeleton = new topaz::SimplicialComplex(topaz::k_skeleton($abs, $k + scalar(@E)));
	my $facet_list_temp2 = $overall_k_skeleton->FACETS;
	#array containing facets
	my @facet_list_temp1 = @$facet_list_temp2;
	my $num_facets = scalar(@facet_list_temp1);
	my @facet_list = map(vectorToArray($facet_list_temp1[$_]), (0..$num_facets - 1));
	#array containing the coordinants of the vertices
	my @vertices_temp = map($comp->COORDINATES->[$comp->VERTEX_INDICES->[$_]], (0..$comp->N_VERTICES - 1));
	my $num_vert = scalar(@vertices_temp);
	my @vertices = map(vectorToArray($vertices_temp[$_]), (0..$num_vert - 1));
	#for each vertex, makes an array of places where it vanishes
	my @vanish_list = map(vanishes($vertices[$_]), (0..$num_vert - 1));
	my @internal_facets = ();
	#for each facet, checks if the intersection of the vanish coordinants is empty
	for my $i (0..$num_facets - 1){
		my @list_of_vanishing = ();
		for my $j (0..scalar(@E) + $k){
			push(@list_of_vanishing, $vanish_list[${$facet_list[$i]}[$j]]);
		}

		my $lc = List::Compare->new(@list_of_vanishing);

		if (scalar($lc->get_intersection) == 0){
			push(@internal_facets, $facet_list[$i]);
		}
	}
	#finds the facets that contain E
	my @hasE = ();
	for my $face (@internal_facets){
		my $lc = List::Compare->new($face, \@E);
		if (scalar($lc->get_intersection) < scalar(@E)){
			next;
		}
		my @rest = $lc->get_unique;
		push(@hasE, \@rest);
	}

	my $s = new topaz::SimplicialComplex(INPUT_FACES=>\@hasE);
	return $s;

}

#usage: ellCoefficient($subdiv, $facet, $i)
#computes ell_i of the facet
#probably i should be less than d/2, although this might be strictly necessary
#uses the formula derived 0.322
#assumes ell_1 = ell_2 = .. = ell_i = 0
sub ellCoefficient{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my $i = shift;
	my $ans = 0;
	my $d = $subdiv->DIM;
	for my $j (0..$i - 1){
		my @faces = subsets(\@facet, $i - $j);
		my $term = 0;
		for my $face (@faces){
			if (excess($subdiv, $face) == $d + 1 - $i){
				#pArr $face;
				$term++;
			}
		}
		#print $term, "\n";
		$ans += powMinusOne($j)*$term;
	}
	return $ans;
}

#checkFacetConjecture($subdiv)
#checks that conjecture that if a facet F can be decomposed into a join of two internal faces
#then ell_i is nonzero
sub checkFacetConjecture{
	my $subdiv = shift;
	my @face = ();
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @facet = @{$facet};
		if (not is_subset(\@facet, \@face)){
			next;
		}
		if (pyramidOverFace($subdiv, $facet, \@face)){
			next;
		}
		my $lc = List::Compare->new(\@facet, \@face);
		my @comp = $lc->get_unique;
		for my $k (0..int(scalar(@comp)/2)){
			my @divisions = subsets(\@comp, $k);
			for my $split (@divisions){
				if (scalar(@{carrier($subdiv, union($split, \@face))}) > 0){
					next;
				}
				my $list = List::Compare->new(\@comp, $split);
				my @other = $list->get_unique;
				if (scalar(@{carrier($subdiv, union(\@face, \@other))}) == 0){
					if (ellCoefficient($subdiv, $facet, $k) < 1){
						pArr $facet;
						return 1;
					}
					last;
				}
			}
		}
	}
	return 0;
}


#usage: generateASubdiv($dim, $n, $number of points)
#generates a single subdivision
#only lifts boundary points
sub generateASubdiv{
	my $dim = shift;
	my $n = shift;
	my $numpoints = shift;
	#computing a regular subdivision requires the vertices of the simplex
	#to be among the points 
	my $boundary_points = getBoundaryNRationalPointsRec($n,$dim+1);
	my $must_have = standard_simplex_vertices($dim);
	#removes the vertices from candidates
	my $count_zeros = 0;
	my $index = 0;
	while ($index < scalar(@{$boundary_points})){
		$count_zeros = 0;
		for my $k (0..($dim)){
			if (($boundary_points->[$index]->[$k]) == 0){
				$count_zeros += 1;
			}
		}
		if ($count_zeros == $dim){
			splice(@{$boundary_points}, $index, 1 );
		} else{
			$index++;
		}
	}

	#randomly choses a subset
	my @rcoords = @{randomSubArray($boundary_points, $numpoints)};
	#adds back in the vertices
	my @baryCoords = map { toBarycentricCoords($_); } @rcoords;
	my $points = union($must_have, \@baryCoords);
	my $baryMat=new Matrix<Rational>($points);
	my $rsub = randomRegularSubdivOfStandardSimplex($baryMat);
	return $rsub;

}


#usage: etaPolynomial($subdiv, $face)
#compute the eta polynomial of the subdivision relative to the face, see 0.353
#does this by enumerating all faces, probably slow
sub etaPolynomial{
	my $subdiv = shift;
	my $E = shift;
	my $E_size = scalar(@{$E});
	my $d = $subdiv->DIM;
	my @result = (0) x ($d + 1 - $E_size);
	my $link;
	if ($E_size > 0){
		$link = new topaz::GeometricSimplicialComplex(topaz::link_complex($subdiv, $E));
	}
	else{
		$link = $subdiv;
	}
	#creates array of the faces
    my $diagram = $link->HASSE_DIAGRAM;
    my @face_list = @{$diagram->FACES};
    shift(@face_list);
    my @face_list2 = map(reindex($link, vectorToArray($_)), @face_list);
    for my $face (@face_list2){
    	my $place = $d + 1 -  $E_size - excess($subdiv, union($E, $face));
    	$result[$place] += powMinusOne($place + scalar(@{$face}));
    }
    return \@result;

}

#usage: findNonContrib($diagram, $subdiv)
#returns all facets such that local h with respect to Q vanishes
#diagram should probably be reduced
sub findNonContrib{
	my $diagram = shift;
	my $subdiv = shift;
	my @vanishing = ();
	my @facets = @{$subdiv->FACETS};
	for my $facet (@facets){
		my @facet = @{$facet};
		my $Q = returnQ($diagram, $subdiv, \@facet);
		if (sumArray(relativeLocalH($subdiv, $Q)) == 0){
			push(@vanishing, \@facet);
		}
	}
	return \@vanishing;
}

#usage: findFixedExcess($subdiv, $face, $k)
#finds all faces of relative excess exactly k
#returns an array of arrays
sub findFixedExcess{
	my $subdiv = shift;
	my @E = @{shift @_};
	my $k = shift;
	my $E_size = scalar(@E);
	my $d = $subdiv->DIM;
	my @result = ();
	my $link;
	if ($E_size > 0){
		$link = new topaz::GeometricSimplicialComplex(topaz::link_complex($subdiv, \@E));
	}
	else{
		$link = $subdiv;
	}
	#creates array of the faces
    my $diagram = $link->HASSE_DIAGRAM;
    my @face_list = @{$diagram->FACES};
    shift(@face_list);
    my @face_list2 = map(reindex($link, vectorToArray($_)), @face_list);
    for my $face (@face_list2){
    	if (excess($subdiv, union(\@E, $face)) == $k){
    		push(@result, $face);
    	}
    }
    return \@result;

}

#usage: etaToH($aref)
#computes the local h polynomial corresponding to the eta polynomial
#could also be used to compute the h polynomial from the f vector
sub etaToH{
	my @eta = @{shift @_};
	my @result = ();
	my $d = scalar(@eta) - 1;
	for my $k (0..$d){
		my $sum = 0;
		for my $j (0..$k ){
			$sum += powMinusOne($k - $j) * binomial($d - $j, $k - $j) * $eta[$j];
		}
		push(@result, $sum);
	}
	return \@result;
}

#usage: etaFacet($ex, $facet)
#computes the eta polynomial of the facet
sub etaFacet{
	my $subdiv = shift;
	my @facet = @{shift @_};
	my $d = $subdiv->DIM;
	my @result;
	for my $i (0..$d + 1){
		my $ans = 0;
		for my $j (0..$i){
			my @faces = subsets(\@facet, $i - $j);
			my $term = 0;
			for my $face (@faces){
				if (excess($subdiv, $face) == $d + 1 - $i){
					$term++;
				}
			}
			$ans += powMinusOne($j)*$term;
		}
		push(@result, $ans);
	}
	return \@result;

}

#usage: sameVariable($diagram, $facet, $facet)
#checks if the two facets are both B_1 in the same variable
#returns 1 if they are, 0 if they are not
#diagram should be reduced
sub sameVariable{
	my $diagram = shift;
	my @facet1 = @{shift @_};
	my @facet2 = @{shift @_};
	my $d = scalar(@facet1);
	for my $i (0..$d - 1){
		my $sum = 0;
		for my $j (0..$d-1){
			$sum += ($diagram->[$facet1[$j]])->[$i];
		}
		if ($sum == 1){
			my $sum2 = 0;
			for my $k (0..$d - 1){
				$sum2 += ($diagram->[$facet2[$k]])->[$i];
			}
			if ($sum2 == 1){
				return 1;
			}
		}
	}
	return 0;
}

#usage: checkBadFacets($diagram, $subdiv)
#diagram must be reduced
#searches for B_1 facets that share a face of codimension 1, don't contribute and are not both B_1 in the same variable
#returns an array of bad pairs
sub checkBadFacets{
	my $diagram = shift;
	my $subdiv = shift;
	my @vanishing = @{findNonContrib($diagram, $subdiv)};
	if (scalar(@vanishing) < 2){
		return [];
	}
	my @pairs = subsets([0..scalar(@vanishing) - 1], 2);
	my @bad = ();
	for my $pair (@pairs){
		#checks if they share a face of cd 1
		my @u = @{union($vanishing[$pair->[0]], $vanishing[$pair->[1]])};
		if (scalar(@u) > scalar(@{$vanishing[0]}) + 1){
			next;
		}
		if (not sameVariable($diagram, $vanishing[$pair->[0]], $vanishing[$pair->[1]])){
			push(@bad, ($vanishing[$pair->[0]], $vanishing[$pair->[1]]));
		}
	}
	return \@bad;
}

#usage: checkABunch($dim, $iter)
#generates a bunch of diagrams
#checks if there is a pair of bad B_1 facets
sub checkABunch{
	my $dim = shift;
	my $iter = shift;
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @bad = @{checkBadFacets($diagram, $subdiv)};
		if (scalar(@bad) > 0){
			pArrArr $diagram;
			pArrArr(\@bad);
		}
	}
}

#usage: isAffIndep(AoA)
#feed a reference to an array of vectors
#returns 1 if the vectors are affine independent
sub isAffIndep{
	my @input = @{shift @_};
	my $d = scalar(@{$input[0]});
	my @vecs = map(new Vector<Rational>($_), @input);
	my @diffs = ();
	for my $i (1..scalar(@vecs) - 1){
		push(@diffs, $vecs[$i] - $vecs[0]);
	}
	my $mat = new Matrix<Rational>(\@diffs);
	if (rank($mat) == scalar(@input) - 1){
		return 1;
	}
	return 0;
}

#usage: noGoodTriangulation($diagram, array of vertices)
#checks if every affinely independent subset of d + 1 of the vertics of the array of vertices is a B_1 facet
#does not check if the actualy facet is a B_1 facet
#in particular, returns 1 on all B_1 facets, including simplicial
#returns 0 if there is a good triangulation, 1 if there is no good triangulation
sub noGoodTriangulation{
	my $diagram = shift;
	my @verts = @{shift @_};
	my $d = scalar(@{$diagram->[0]});
	my @subs = subsets(\@verts, $d);
	for my $vertices (@subs){
		my @coords = map($diagram->[$_], @{$vertices});
		if (not isAffIndep(\@coords)){
			next;
		}
		if (not isLatticePyramid($diagram, $vertices)){
			return 0;
		}
	}
	return 1;
}

#usage: isB1Facets(diagram, array of vertices)
#checks if the facet is a B_1 facets
#does not assume that the facet is simplicial
#does not check if it is B_1
sub isB1Facet{
	my $diagram = shift;
	my @verts = @{shift @_};
	my $d = scalar(@{$diagram->[0]});
	for my $i (0..$d - 1){
		my $sum = 0;
		for my $j (0..scalar(@verts) - 1){
			$sum += ($diagram->[$verts[$j]])->[$i];
		}
		if ($sum == 1){
			return 1;
		}
	}
	return 0;

}

#usage: hasBadFacet($diagram)
#diagram does not need to be reduced
#only interesting if the associated polytope is not simplicial
#checks if the diagram has a non-simplicial facet such that every triangulation consists of B_1 facets
#returns 0 if no bad facets, 1 if there is a bad facet
sub hasBadFacet{
	my $diagram = shift;
	my $proj = toProjectiveArray($diagram);
	my $shifted = shiftToInfinity($proj);
	my @new = @{deProjective($shifted)};
	#points are now in the form (points in simplex in R^d, weight)
	my @weighvec = ();
	for my $i (0.. scalar(@new) - 1){
		$weighvec[$i] = pop(@{$new[$i]});
	}
	my $coords = toStandard(\@new);
	my @baryCoords = map(toBarycentricCoords($_), @{$coords});


	my $dim = scalar(scalar(@{$diagram->[0]}));
	my $weightsRef = new Vector<Rational>(\@weighvec);
 	my $baryMat=new Matrix<Rational>(\@baryCoords);
    my $subdiv = new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat, 
    	INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
    #checks if it is a triangulation
    if ($subdiv->DIM == $dim - 1){
    	return 0;
    }
    $diagram = removeRedundant($diagram, $subdiv);
 	my @flist = @{$subdiv->FACETS};
 	for my $f (@flist){
 		my @f = @{$f};
 		#checks if facet is simplicial
 		if (scalar(@f) == $dim - 1){
 			next;
 		}
 		if (isB1Facet($diagram, $f)){
 			next;
 		}
 		if (noGoodTriangulation($diagram, $f)){
 			return 1;
 		}
 	}
 	return 0;   
}

#usage: lookForBad($dim, $iter)
#generates a bunch of random subdivs, checks if they are bad
#reutnrs the diagrams
sub lookForBad{
	my $dim = shift;
	my $iter = shift;
	my @bad = ();
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 15, 40);
		if (hasBadFacet($diagram)){
			push(@bad, $diagram);
		}
	}
	return \@bad;
}
#usage: facetToCoords($diagram, $facet)
#diagram must be reduced
#returns an array of arrays of the coordinates of the facet
sub facetToCoords{
	my $diagram = shift;
	my @facet = @{shift @_};
	my @coords = map($diagram->[$_], @facet);
	return \@coords;
}


#usage: returnBadFacets($diagram)
#returns an array containing the vertex coordinates of the bad facets
sub returnBadFacets{
	my $diagram = shift;
	my @bad = ();
	my $proj = toProjectiveArray($diagram);
	my $shifted = shiftToInfinity($proj);
	my @new = @{deProjective($shifted)};
	#points are now in the form (points in simplex in R^d, weight)
	my @weighvec = ();
	for my $i (0.. scalar(@new) - 1){
		$weighvec[$i] = pop(@{$new[$i]});
	}
	my $coords = toStandard(\@new);
	my @baryCoords = map(toBarycentricCoords($_), @{$coords});


	my $dim = scalar(scalar(@{$diagram->[0]}));
	my $weightsRef = new Vector<Rational>(\@weighvec);
 	my $baryMat=new Matrix<Rational>(\@baryCoords);
    my $subdiv = new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat, 
    	INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
    #checks if it is a triangulation
    if ($subdiv->DIM == $dim - 1){
    	return 0;
    }
    $diagram = removeRedundant($diagram, $subdiv);
 	my @flist = @{$subdiv->FACETS};
 	for my $f (@flist){
 		my @f = @{$f};
 		#checks if facet is simplicial
 		if (scalar(@f) == $dim - 1){
 			next;
 		}
 		if (isB1Facet($diagram, $f)){
 			next;
 		}
 		if (noGoodTriangulation($diagram, $f)){
 			push(@bad, $f);
 		}
 	}
 	my @final = map(facetToCoords($diagram, $_), @bad);
 	return \@final;
}




#usage: projToSimplex(array of coordinates, indices to project to)
#computes the projection to these indices
#returns one if the result is the standard simplex
#assumes that no column contains all 0s
sub projToSimplex{
	my @coords = @{shift @_};
	my @sub = @{shift @_};
	for my $i (0..scalar(@coords) - 1){
		my $sum = 0;
		for my $index (@sub){
			$sum += $coords[$i]->[$index];
		}
		if ($sum > 1){
			return 0;
		}
	}
	return 1;
}



#usage: BkFacet($coordinates, array of vertices)
#returns the biggest k such that the facet is B_k
#does not work for B_1, facet should be bad
#returns 1 if it is not a B_2 facet
#use with BkFacet(returnBadFacets($list[$i])->[0])
sub BkFacet{
	my @coords = @{shift @_};
	my $d = scalar(@{$coords[0]} - 1);
	my $nverts = scalar(@coords);
	for my $i (2..$d - 1){
		my $found = 0;
#		my @fibers = ();
		my @subsets = subsets([0..$d], $i);
		my @used = ();
		for my $sub (@subsets){
			if (projToSimplex(\@coords, $sub)){
				$found = 1;
				last;
			}
		}
		if ($found == 0){
			return $i - 1;
		}
		if ($found == 1 and $i == $d - 1){
			return $i;
		}
	}
}

#usage: writeSubdivToFile($list of subdivs, filename)
#file with filename should already exist
#need to give the full path
sub writeSubdivToFile{
	my @list = @{shift @_};
	my $filename = shift;
	open(my $fh, '>', $filename) or die "Could not open file '$filename' $!";
	print $fh "144169\n";
	for my $subdiv (@list){
		#prints facets
		my @flist = @{$subdiv->FACETS};
		for my $i (0..$subdiv->N_FACETS - 1){
			my @f = @{$flist[$i]};
			print $fh "@f", "\n";
		}
		print $fh "2399", "\n";
		#prints the vertices such that the carrier of each vertex contains the ith vertex
		my $d = $subdiv->DIM + 1;
		my @carried = () x $d;	
		for my $j (0..$subdiv->N_VERTICES - 1){
			my @carrier = @{carrier($subdiv, [$j])};
			my $lc = List::Compare->new([0..$d], \@carrier);
			my @good = $lc->get_unique;
			for my $vertex (@good){
				push(@{$carried[$vertex]}, $j);
			}
		}
		for my $i (0..$d - 1){
			print $fh "@{$carried[$i]}", "\n";
		}
		print $fh "1728", "\n";
		#prints the faces to test, i.e. the faces which admit a decomposition.
		my @decomp = ();
		for my $facet (@flist){
			my @facet = @{$facet};
			for my $k (0..int((scalar(@facet) + 1)/2)){
				my @divisions = subsets(\@facet, $k);
				for my $split (@divisions){
					if (scalar(@{carrier($subdiv, $split)}) > 0){
						next;
					}
					my $list = List::Compare->new(\@facet, $split);
					my @other = $list->get_unique;
					if (scalar(@{carrier($subdiv, \@other)}) == 0){
						push(@decomp, $split);
						push(@decomp, \@other);
					}
				}
			}
		}

		my @tocheck = @{removeDuplicates(\@decomp)};
		for my $i (0..scalar(@tocheck) - 1){
			print $fh "@{$tocheck[$i]}", "\n";
		}
		print $fh "144169\n";
	}


}

#usage: writeRandomTriangulation(dim, points, iter)
#gets a bunch (iter) of random triangulation of the dim-sphere with points number of points
#writes them to the files "sphere.txt"
sub writeRandomTriangulation{
	my $dim = shift;
	my $points = shift;
	my $iter = shift;
	open(my $fh, '>', 'spheres.txt') or die "Could not open file '$filename' $!";
	print $fh "144169\n";

	for my $i (0..$iter - 1){
		my $p = rand_sphere($dim, $points);
		my @facets = @{$p->FACET_LABELS};
		for my $f (@facets){
			my @array = split(",", $f);
			print $fh "@array", "\n";
		}
		print $fh "2399", "\n";
		print $fh "1729", "\n";
		for my $f (@facets){
			my @array = split(",", $f);
			print $fh "@array", "\n";
		}
 		print $fh "144169\n";

	}

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

#usage:generateABunchOfDiagrams(dimension, number of iterations)
#returns a bunch of reduced that give triangulations
#may return fewer diagrams because the random diagrams it generates might be non-simplicial
sub generateABunchOfDiagrams{
	my $dim = shift;
	my $iter = shift;
	my @diagrams = ();
	for my $i (0..$iter){
		my $diagram = sumRND($dim, 10000, 20, 50);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		push(@diagrams, $diagram);
	}
	return \@diagrams;
}

#usage:returnB1Facets($diagram, $subdiv)
#diagram should be reduced
#returns an AoA of all B1 facets
sub returnB1Facets{
	my $diagram = shift;
	my $subdiv = shift;
	my $nfacets = $subdiv->N_FACETS;
	my @B1s = ();
	for my $i (0..$nfacets - 1){
		my @facet = @{$subdiv->FACETS->[$i]};
		if (isLatticePyramid($diagram, \@facet)){
			push(@B1s, \@facet);
		}
	}
	return \@B1s;
}


#usage: lookForCD2(diagram)
#diagram should be reduced, give a triangulation
#Finds all faces that are contained in a non-pyrmidal facet and are also Q for a B_1 facets and have carrier codim 2, excess at least 2
#returns 1 if there is such a face, returns 0 if there isn't
sub lookForCD2{
	my $diagram = shift;
	my $subdiv = diagramToSubdiv($diagram);
	my $dim = $subdiv->DIM;
	my @npyramidal = @{returnNonPyramidalFaces($subdiv)};
	my @smallcodim;
	my @candidates;
	for my $facet (@npyramidal){
		my @tocheck = subarrs(@{$facet});
		#pArrArr(\@tocheck);
		@candidates = @{AoAUnion(\@tocheck, \@candidates)};
	}
	#check which of the faces has carrier codimension 2
	for my $face (@candidates){
		if ((scalar(@{carrier($subdiv, $face)}) == 2)and (excess($subdiv, $face) > 1)){
			push(@smallcodim, $face);
		}
	}

	#find all B_1 facets, find Q for each
	#check if any of these faces is Q of a B_1 facet

	my @B1s = @{returnB1Facets($diagram, $subdiv)};
	for my $facet (@B1s){
		my $Q = returnQ($diagram, $subdiv, $facet);
		for my $face (@smallcodim){
			if (entrywiseEquality($Q, $face) == 1){
				pArr($face);
				pArr($facet);
				pArrArr($diagram);
				pArr(relativeLocalH($subdiv, $face));
				return 1;
			}
		}
	}

	return 0;
}




#usage: NonSimpRemoveRedundant(diagram)
#takes a diagram, removes the points that don't contribute to the subdivision
#works without assuming that the subdiision is simplicial
#returns the reduced diagram
sub nonSimpRemoveRedundant{
	my $diagram = shift;
	my $subdiv = nonSimpDiagramToSubdiv($diagram); 
	my @good = @{$subdiv->VERTEX_INDICES};
	my @relevant_faces = ();
	for my $index (@good){
		push(@relevant_faces, $diagram->[$index]);
	}

	return \@relevant_faces;
}

#usage: perturbNonSimp(diagram)
#diagram should be reduced
#adds a small random number to vertex other than the vertices that make it convenient
#this can be used to compute a random triangulation
sub perturbNonSimp{
	my $diagram = shift;
	my @newdiagram;
	my $dim = scalar(@{$diagram->[0]});
	for my $vertex (@{$diagram}){
		#counts number of entries that are non-zero
		my $numnon0 = 0;
		my @newvert;
		for my $index (0..($dim - 1)){
			if ($vertex->[$index] == 0){
				$numnon0 += 1;
			}
		}
		if ($numnon0 == $dim - 1){
			push(@newdiagram, $vertex);
			next;
		}
		for my $index (0..($dim - 1)){
			push(@newvert, $vertex->[$index] + rand()/1000);
		}
		push(@newdiagram, \@newvert);

	}
	return \@newdiagram;

}


#usage:findTriangulated($diagram, $triangulateddiagram, $facet)
#$facet should be a (non-simplicial) facet of the original diagram
# this non-simplicial facet is randomly triangulated by $triangulateddiagram
#this returns an AoA giving the trinagulating facets
sub findTriangulated{
	my $diagram = shift;
	my $triangulateddiagram = shift;
	my $facet = shift;
	my $subdiv = diagramToSubdiv($triangulateddiagram);
	my @faces;
	my $dim = scalar(@{$triangulateddiagram->[0]});
	my @candidates = subsets($facet, $dim);
	for my $candidate (@candidates){
		if (isFace($subdiv, $candidate)){
			push(@faces, $candidate);
		}
	}
	return \@faces;
}

#usage: computeMultiplicity($diagram, $facet)
#not necessary unless the facet is non-simplicial
#computes the contribution to the multiplicity of the corresponding eigenvalue
sub computeMultiplicity{
	my $diagram = shift;
	my $facet = shift;
	my $reduceddiagram = nonSimpRemoveRedundant($diagram);
	my $perturbed = perturbNonSimp($reduceddiagram);
	my $subdiv = diagramToSubdiv($perturbed);
	my $contributingfacets = findTriangulated($reduceddiagram, $perturbed, $facet);
	my $mult = 0;
	for my $face (@{$contributingfacets}){
		pArr($face);
		#uses 3 because the 2nd argument of returnQ isn't necessary, and I'm too lazy to fix it
		my $Q = returnQ($reduceddiagram, 3, $face);
		my $local_h = relativeLocalH($subdiv, $Q);
		$mult += sumArray($local_h);
	}
	return $mult;
}











