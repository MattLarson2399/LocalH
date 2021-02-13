#!/usr/bin/perl
#Contributors: Jason Schuchardt and Matt Larson
#Last updated: 01/29/2021

#contains various useful scripts
#does not have specific things designed to test specific conjectures


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

script("/Users/matthew/Desktop/Local_Zeta_Function/code/utilities.pl");

#this file contains general operations with subdivisions and for computing with local h
#and Newton polyhedra 
#One needs to be very careful when working with non-simplicial subdivisions 


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





# computes as alternating sum of H_VECTORs
#not fastest, relativeLocalH is faster
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
#checks if the entire subdivision is a cone over a face
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
#returns the number of ordered pairs where the underlying abstract simplicial complexes are isomorphic
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
#i.e. the dimension of the carrier - dim face
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
#checks if all maximal faces are pyramids 
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


#usage: relativeLocalH(subdivision, facet)
#computes relative local h as a sum of alternating h-vectors
#faster than local_h
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
	#my $trans = pdl(\@mat);
	my $trans = new Matrix <Rational>(\@mat);

	#applies the transformation
	my @output = ();
	for my $i (0..scalar(@points) - 1){
		#my $pvecT = pdl $points[$i];
		#my $pvec = pdl $pvecT->transpose;
		my $vec = new Vector<Rational>($points[$i]);
		my $res = $trans*$vec;
		#my @result = $res->list;
		push(@output, $res);
		
	}
	return \@output;
}
#usage: deProjective(AoA)
#takes an array of arrays, scales so that the last coordinant is 1
#then removes the last coordinant
sub deProjective{
	my @points = @{shift @_};
	my $dim = scalar(@{$points[0]});
	my @output = ();
	for my $i (0.. scalar(@points) - 1){
		my @vec = ();
		for my $j (0..$dim - 2){
			if ($points[$i]->[$j] == 0){
				$vec[$j] = 0;
				next;
			}
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


#usage: nonSimpDiagramToSimp(AoA)
#treats the array of arrays as an array of points
#all points should have the same dimension, should include the standard basis vectors (must be convenient)
#does not check if the subdivision is a triangulation
#returns a simplicial complex even if isn't simplicial
#can be used to reduce a diagram
sub nonSimpDiagramToSimp{
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

#usage: posNegDecomp($diagram, $facet)
#expresse (1,...,1) as a linear combination of vertices in the facet
#returns AoA of the vertices that are not in Q that are positive and the vertices that are non-positive
sub posNegDecomp{
	my $diagram = shift;
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
	my @pos = ();
	my @neg = ();
	my @res = $res->list;
	for my $j (0..$dim){
		if (abs($res[$j] - round($res[$j])) > 0.00000001){
			next;
		}
		if ($res[$j] > 0.00000001){
			push(@pos, $facet->[$j]);
			next;
		}
		if ($res[$j] < 0.00000001){
			push(@neg, $facet->[$j]);
			next;
		}
	}
	return [\@pos, \@neg];

}

#usage: returnLinearExpression($diagram, $facet)
#expresse (1,...,1) as a linear combination of vertices in the facet
#returns coefficients
sub returnLinearExpression{
	my $diagram = shift;
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
	my @res = $res->list;
	return \@res;

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

#usage: addTypeGraph($list, $graphs)
#finds the type graph of every facet in the list, adds the isomorphism classes to those already in $graphs
#graphs should be a list of isomoprhism classes.
#returns the list
sub addTypeGraph{
	my $list = shift;
	my $graphs = shift;
	my @newgraphs;
	for my $subdiv (@{$list}){
		my @facets = @{$subdiv->FACETS};
		for my $f (@facets){
			push(@newgraphs, typeGraph($subdiv, \@{$f}));
		}
	}
	#removes those already in $graphs
	for my $g (@newgraphs){
		my $new = 1;
		for my $graph (@{$graphs}){
			if (isomorphic($g, $graph)){
				$new = 0;
				last;				
			}

		}
		if ($new == 1){
			push(@{$graphs}, $g);
		}
	}
	return $graphs;

}


#usage: writeTypeGraph(list of type graphs, filename)
#graphs should be simplicial complexes
#filename should already exist, need to give the full path
#writes to a file in the form of a list of edges on each line
#the vertices numbered 0-dim are the vertices, other vertices are the faces. 
sub writeTypeGraph{
	my $list = shift;
	my $filename = shift;
	open(my $fh, '>', $filename) or die "Could not open file '$filename' $!";
	for my $f (@{$list}){
		my @facets = @{$f->FACETS};
		for my $edge(@facets){
			my @edge = @{$edge};
			print $fh "($edge[0],$edge[1])";
		}
		print $fh "\n";
	}
}

#usage: skelToGraph(1-dimensional simplicial complex)
#returns a graph of that complex
sub skelToGraph{
	my $simp = shift;
	my @edges = map(vectorToArray($_), @{$simp->FACETS});
	return graph_from_edges(\@edges);
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


#usage: numberDecomposition($subdiv, $facet, $face)
#computes the number of decompositions of the facet into G_1 \cup G_2 \cup face, G_1, G_2 relatively interior 
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
#this is only indirectly checking if they are B_1 because non-contributing facets must be B_1
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

#usage: allBadB1($diagram, $subdiv)
#diagram must be reduced
#find all pairs of B_1 facets that share a face of codimension 1 and are not both B_1 in the same variable
#and also contribute the same candidate pole
#so finds all B-borders
sub allBadB1{
	my $diagram = shift;
	my $subdiv = shift;
	my @bs = @{returnB1Facets($diagram, $subdiv)};
	my @fs = map(vectorToArray($_), @bs);
	my @pairs = subsets([0..scalar(@fs) - 1], 2);
	my @bad = ();
	for my $pair (@pairs){
		#checks if they share a face of cd 1
		my @u = @{union($fs[$pair->[0]], $fs[$pair->[1]])};
		if (scalar(@u) > scalar(@{$fs[0]}) + 1){
			next;
		}
		if (not sameVariable($diagram, $fs[$pair->[0]], $fs[$pair->[1]])){
			if ((candidatePole($diagram, $fs[$pair->[0]]) - candidatePole($diagram, $fs[$pair->[1]])) == 0){
				push(@bad, ($fs[$pair->[0]], $fs[$pair->[1]]));
			}
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
	my @list;
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @bad = @{allBadB1($diagram, $subdiv)};
		if (scalar(@bad) > 0){
			push(@list, $diagram);
		}
	}
	return \@list;
}

#usage: bunchOfPotentiallyBad($dim, $iter)
#generates a bunch of diagrams
#checks if they have a pair of B_1 facets that intersect in a face of codimension 1, not in the same variable
#that also contribute the same candidate pole
#does not check if local h relative to them vanishes
sub bunchOfPotentiallyBad{
	my $dim = shift;
	my $iter = shift;
	my @list;
	for my $i (0..$iter - 1){
		my $diagram = sumRND($dim, 10000, 15, 20);
		my $subdiv = diagramToSubdiv($diagram);
		if ($subdiv == 1){
			next;
		}
		$diagram = removeRedundant($diagram, $subdiv);
		my @bad = @{allBadB1($diagram, $subdiv)};
		if (scalar(@bad) > 0){
			if ((candidatePole($diagram, $bad[0]) - candidatePole($diagram, $bad[1])) == 0){
				push(@list, $diagram);
			}
		}
	}
	return \@list;

}


#usage: checkIfBorder($diagram, $facet1, $facet2)
#checks if the facets are a B^2 border 
#checks if they are both B_1 facets that are not B_1 in the same variable and share a face of cd 1- returns -1 if not
#checks if the middle face looks like a B^2 border
#returns the number of peaks
#if number of peaks is at least 3, then it is well-structured
sub checkIfBorder{
	my $diagram = shift;
	my $facet1 = shift;
	my $facet2 = shift;
	my $dim = scalar(@{$facet1});

	#finds the common face
	#need to test this
	my $lc = List::Compare->new(($facet1, $facet2));
	my @intersection = $lc->get_intersection;
	@intersection = sort {$a <=> $b} @intersection;
	#checks if share a face of cd 1
	if (scalar(@intersection) != ($dim - 1)){
		return -1;
	}
	#checks if they are B_1 in same variable
	if (sameVariable($diagram, $facet1, $facet2)){
		return -1;
	}
	#looks for coordinates in the intersection that have only one 1
	my @candidates;
	for my $i (0..$dim - 1){
		my $sum = 0;
		for my $v (@intersection){
			$sum += ($diagram->[$v])->[$i];
		}
		if ($sum == 1){
			push(@candidates, $i);
		}
	}
	#I think that if #candidates > 2, then it should be a border
	return scalar(@candidates);
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

#usage: isB1Facet(diagram, array of vertices)
#checks if the facet is a B_1 facets
#does not assume that the facet is simplicial
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


#usage:generateABunchOfDiagrams(dimension, number of iterations)
#returns a bunch of reduced that give triangulations
#may return fewer diagrams because the random diagrams it generates might be non-simplicial
#produces reduce diagrams!
sub generateABunchOfDiagrams{
	my $dim = shift;
	my $iter = shift;
	my @diagrams = ();
	for my $i (0..$iter){
		my $diagram = sumRND($dim, 50, 15, 6);
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
	my $subdiv = nonSimpDiagramToSimp($diagram); 
	my @good = @{$subdiv->VERTEX_INDICES};
	my @relevant_faces = ();
	for my $index (@good){
		push(@relevant_faces, $diagram->[$index]);
	}

	return \@relevant_faces;
}

#usage: perturbNonSimp(diagram)
#diagram should be reduced
#adds a small random number to vertices
#adds to the entries that are non-zero
#this can be used to compute a random triangulation
sub perturbNonSimp{
	my $diagram = shift;
	my @newdiagram;
	my $dim = scalar(@{$diagram->[0]});
	for my $vertex (@{$diagram}){
		my @newvert;
		for my $index (0..($dim - 1)){
			if($vertex->[$index] != 0){
				push(@newvert, $vertex->[$index] + round(rand()*10000)/1000000);
				next;
			}
			push(@newvert, $vertex->[$index]);
	
		}
		push(@newdiagram, \@newvert);

	}
	return \@newdiagram;

}


#usage: checkGoodTri($diagram, perturbed diagram)
#bad things that can when happen when perturbing: one of the facets might not be affine independent
#or we could lose a vertex
#checks for both
#returns 0 if it is not good, 1 if it is goods
sub checkIfGoodTri{
	my $diagram = shift;
	my $perturbed = shift;
	my $dim = scalar(@{$perturbed->[0]});
	my $subdiv = diagramToSubdiv($perturbed);
	my $numverts = scalar(@{$diagram});
	if (($subdiv->N_VERTICES) != $numverts){
		return 0;
	}
	my @flist = @{$subdiv->FACETS};
	for my $facettemp (@flist){
		my @facet = @{$facettemp};
		my @vertices;
		for my $i (0..$dim - 1){
			push(@vertices, $diagram->[$facet[$i]]);
		}
		if(isAffIndep(\@vertices) == 0){
			pArr(\@facet);
		}
	}
	return 1;


}





#usage:findTriangulated($diagram, $triangulatedsubdiv, $facet)
#$facet should be a (non-simplicial) facet of the original diagram
# this non-simplicial facet is randomly triangulated by $triangulateddiagram
#this returns an AoA giving the trinagulating facets
sub findTriangulated{
	my $diagram = shift;
	my $subdiv = shift;
	my $facet = shift;
	my @faces;
	my $dim = $subdiv->DIM + 1;
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
#probably the diagram should be reduced
sub computeMultiplicity{
	my $diagram = shift;
	my $facet = shift;
	my $reduceddiagram = nonSimpRemoveRedundant($diagram);
	#finds a good perturbed subdivision
	my $i = 0;
	my $perturbed = 0;
	while($i < 100){
		$perturbed = diagramToPerturbedSubdiv($reduceddiagram);
		if($perturbed->N_VERTICES == scalar(@{$reduceddiagram})){
			$i = 100;
		}
		if ($i == 99){
			print "No good triangulation found";
			return -1;
		}
		$i += 1;
	}
	my $contributingfacets = findTriangulated($reduceddiagram, $perturbed, $facet);
	my $mult = 0;
	for my $face (@{$contributingfacets}){
		#uses 3 because the 2nd argument of returnQ isn't necessary, and I'm too lazy to fix it
		my $Q = returnQ($reduceddiagram, 3, $face);
		my $local_h = relativeLocalH($perturbed, $Q);
		$mult += sumArray($local_h);
	}
	return $mult;
}


#usage: localHTriangulated($diagram, triangulated simplex, $facet)
#returned the local h polynomials associated to that facet
#diagram should be reduced
sub localHTriangulated{
	my $diagram = shift;
	my $perturbed = shift;
	my $facet = shift;
	my $contributingfacets = findTriangulated($diagram, $perturbed, $facet);
	my @localh;
	for my $face (@{$contributingfacets}){
		#uses 3 because the 2nd argument of returnQ isn't necessary, and I'm too lazy to fix it
		my $Q = returnQ($diagram, 3, $face);
		my $local_h = relativeLocalH($perturbed, $Q);
		push(@localh, $local_h);
	}
	return \@localh;

}


#usage: returnNonSimpFacets($diagram)
#diagram needs to be full reduced
#returns all non-simplicial facets
sub returnNonSimpFacets{
	my $diagram = shift;
	my $dim = scalar(@{$diagram->[0]});
	my $subdiv = nonSimpDiagramToSimp($diagram);
	my @flist = @{$subdiv->FACETS};
	my @nonsimp;
	for my $facet (@flist){
		if(scalar(@{$facet}) > $dim){
			my @f = @{$facet};
			push(@nonsimp, \@f);
		}
	}
	return \@nonsimp;
}

#usage: computeMultiplicityAllNonSimp($diagram)(
#diagram should be fully reduced
#returns an arref with all eigenvalues
sub computeMultiplicityAllNonSimp{
	my $diagram = shift;
	my @nonsimp = @{returnNonSimpFacets($diagram)};
	my @results;
}


#usage: saveDiagram($list of polytopes, corresponding list of diagrams, name)
#takes a list of polytopes and corresponding list of diagrams
sub saveDiagrams{
	my @polylist = @{shift @_};
	my $dgramlist = shift;
	my $name = shift;
	for my $i (0..scalar(@polylist) - 1){
		$polylist[$i]->name = diagramToString($dgramlist->[$i]);
	}
	script("tarballs");
	my $file_name = $name . '.tgz';
	pack_tarball($file_name, @polylist);

}


#usage: loadDiagram(name)
#loads the diagram
#outputs an ARRAY containing arrefs to the array of polytopes, corresponding array of diagrams
sub loadDiagrams{
	script("tarballs");
	my $name = shift;
	my $file = $name . ".tgz";
	my @list = unpack_tarball($file);
	my @diagrams = ();
	for my $poly (@list){
		push(@diagrams, stringToDiagram($poly->name));
	}
	return(\@list, \@diagrams);
}

#usage: diagramToPerturbedSubdiv(AoA)
#treats the array of arrays as an array of points
#all points should have the same dimension, should include the standard basis vectors (must be convenient)
#perturbs the weights to make it a triangulation
sub diagramToPerturbedSubdiv{
	my $diagram = shift;
	my $dim = scalar(scalar(@{$diagram->[0]}));
	my $proj = toProjectiveArray($diagram);
	my $shifted = shiftToInfinity($proj);
	my @new = @{deProjective($shifted)};
	#points are now in the form (points in simplex in R^d, weight)
	#perturbs weights
	for my $i (0..(scalar(@new) - 1)){
		$new[$i]->[$dim - 1] = $new[$i]->[$dim - 1] + round(rand()*1000000)/100000000000000;
	}
	my @weighvec = ();
	for my $i (0.. scalar(@new) - 1){
		$weighvec[$i] = pop(@{$new[$i]});
	}
	my $coords = toStandard(\@new);
	my @baryCoords = map(toBarycentricCoords($_), @{$coords});
	#pArrArr(\@baryCoords);

	my $weightsRef = new Vector<Rational>(\@weighvec);
 	my $baryMat=new Matrix<Rational>(\@baryCoords);

 	#hackish fix to make it triangulate properly
 	#my $fan = new fan::SubdivisionOfPoints(POINTS=>$baryMat, WEIGHTS=>$weightsRef);
 	#my $complex = $fan->POLYHEDRAL_COMPLEX;
 	#my $polyfacets = $complex->N_MAXIMAL_POLYTOPES;

 	#print $baryMat;
    my $subdiv = new topaz::GeometricSimplicialComplex(COORDINATES=>$baryMat, 
    	INPUT_FACES=>regular_subdivision($baryMat, $weightsRef));
    #if ($subdiv->N_FACETS != $polyfacets){
    #	print "Different subdivisions";
    #}
    #checks if it is not a triangulation
    if ($subdiv->DIM == $dim - 1){
    	return $subdiv;
    }
    return 1;

}
#usage: totalEigenvalues($diagram)
#perturbs diagram, then computes the sum of the multiplicity of all eigenvalues
sub totalEigenvalues{
	my $diagram = shift;
	my $reduceddiagram = nonSimpRemoveRedundant($diagram);
	my $mult = 0;
	#finds a good perturbed subdivision
	my $i = 0;
	my $perturbed = 0;
	#while($i < 100){
	$perturbed = diagramToPerturbedSubdiv($reduceddiagram);
	if($perturbed->N_VERTICES != scalar(@{$reduceddiagram})){
		print "No good triangulation found";
		return -1;
	}

	my @contributingfacets = @{$perturbed->FACETS};
	for my $i (0..($perturbed->N_FACETS - 1)){
		#uses 3 because the 2nd argument of returnQ isn't necessary, and I'm too lazy to fix it
		my @facettocheck = @{$contributingfacets[$i]};
		my $Q = returnQ($reduceddiagram, 3, \@facettocheck);
		my $local_h = relativeLocalH($perturbed, $Q);
		$mult += sumArray($local_h);
	}
	return $mult;
}

#usage: checkIfConvex(AoA)
#takes a finite set of points
#returns -1 if the points are in convex position
#returns the indices of the vertices that are in the convex hull of the others
sub checkIfConvex{
	my $points = shift;
	my $num = scalar(@{$points});
	my $proj = toProjectiveArray($points);
	my $p = new Polytope(POINTS=>$proj);
	my $realnum = $p->N_VERTICES;
	my @normalized = map {toBarycentricCoords($_)} @{$points};
	#need to normalize points to make sum 1
	if ($num == $realnum){
		return -1;
	}
	my @vertices = @{$p->VERTICES};
	my @badindex;
	my $counter = 0;
	for my $i (0..($num -1)){
		if ($counter == $realnum){
			push(@badindex, $i);
			next;
		}
		my $array =  vectorToArray($vertices[$counter]);
		pop(@{$array});
		if (entrywiseEquality($array, $normalized[$i]) == 1){
			$counter += 1;
			next;
		}
		push(@badindex, $i);
	}
	return \@badindex;
}


#usage: fixConvexFacet($diagram, array of indices of vertices)
#in most uses, the vertices will be an allegedly non-simplicial facet
#checks if some of the vertices are in the convex hull of the those vertices
#returns the diagram with vertices removed
sub fixConvexFacet{
	my $diagram = shift;
	my @facet = @{shift @_};
	my @points;
	for my $index (@facet){
		push(@points, $diagram->[$index]);
	}
	my $result = checkIfConvex(\@points);
	if ($result == -1){
		return $diagram;
	}
	my @d = @{$diagram};
	my $numdel = scalar(@{$result});
	#splices in reverse order
	for my $i (0..($numdel - 1)){
		splice @d, $facet[$result->[$numdel - $i - 1]], 1;
	}
	return \@d;
}

#usage: furtherReduceDiagram($diagram)
#only interesting if polymake is claiming the diagram is non-simplicial
#takes a diagram, which should probably already be reduced, and looks through the allegedly non-simpllcial facets
#if the facet has fake vertices, then it removes them
#only removes vertices from one facet
#returns [diagram, 0] if it made changes, [diagram, 1] if it did not make changes
sub furtherReduceDiagram{
	my $diagram = shift;
	my $numvert = scalar(@{$diagram});
	#finds allegedly non-simplicial facets
	my $dim = scalar(@{$diagram->[0]});
	my $subdiv = nonSimpDiagramToSimp($diagram);
	my @flist = @{$subdiv->FACETS};
	my @nonsimp;
	for my $facet (@flist){
		if(scalar(@{$facet}) > $dim){
			my @f = @{$facet};
			push(@nonsimp, \@f);
		}
	}
	for my $face(@nonsimp){
		$diagram = fixConvexFacet($diagram, $face);
		if (scalar @{$diagram} < $numvert){
			return [$diagram, 0];
		}
	}
	return [$diagram, 1]
}
#usage: completelyReduceDiagram($diagram)
#takes a diagram, doesn't assume it to be reduced
#removes all fake vertices and reduces it
#same as removeRedundant in the simplicial case
sub completelyReduceDiagram{
	my $diagram = shift;
	$diagram = nonSimpRemoveRedundant($diagram);
	my $indicator = 0;
	while ($indicator == 0){
		my $result = furtherReduceDiagram($diagram);
		$diagram = $result->[0];
		$indicator = $result->[1];
	}
	return $diagram;
}

#usage: nonSimplicialEigenvalues($diagram)
#returns an array containing the multiplicity that each non-simplicial facet contibutes
sub nonSimplicialEigenvalues{
	my $diagram = shift;
	my @nonsimp = @{returnNonSimpFacets($diagram)};
	my @eigenvalues;
	for my $facet (@nonsimp){
		push(@eigenvalues, computeMultiplicity($diagram, $facet));
	}
	return \@eigenvalues;
}

#usage: isB1Facets(AoA)
#checks if the facet is a B_1 facets
#does not assume that the facet is simplicial
#input is an array of coordates of the vertices
sub facetB1{
	my @facet = @{shift @_};
	my $d = scalar(@{$facet[0]});
	for my $i (0..$d - 1){
		my $sum = 0;
		for my $j (0..scalar(@facet) - 1){
			$sum += ($facet[$j])->[$i];
		}
		if ($sum == 1){
			return 1;
		}
	}
	return 0;

}

#usage: checkForUniversallyB1($diagram)
#diagram should be fully reduced
#returns 1 if it has a universally B_1 facet
sub checkForUniversallyB1{
	my $diagram = shift;
	my @nonsimplicial = @{returnNonSimpFacets($diagram)};
	for my $facet (@nonsimplicial){
		if (isB1Facet($diagram, $facet)){
			next;
		}
		if (noGoodTriangulation($diagram, $facet)){
			return 1;
		}
	}
	return 0;

}


#usage: returnUniversallyB1($diagram)
#returns an AoA containing the universally B1 facets
sub returnUniversallyB1{
	my $diagram = shift;
	my @nonsimplicial = @{returnNonSimpFacets($diagram)};
	my @univ;
	for my $facet (@nonsimplicial){
		if (isB1Facet($diagram, $facet)){
			next;
		}
		if (noGoodTriangulation($diagram, $facet)){
			push(@univ, $facet);
		}
	}
	return \@univ;



}

#usage: normal(AoA)
#take an array of a bunch of vertices 
#returns a normal vector 
#only looks at the first n vectors
sub normal{
	my $vectors = shift;
	my @rows;
	my @first = @{$vectors->[0]};
	for my $i (1..(scalar(@first) - 1)){
		my @row;
		for my $j (0..(scalar(@first) - 1)){
			push(@row, $first[$j] - $vectors->[$i]->[$j])
		}
		#push(@row, 0);
		push(@rows, \@row);
	}
	#pads matrix with an extra row to determine the system and hopefully get integral coefficients
	my @extra = (1) x (scalar(@first));
#	pArrArr(\@rows);
	push(@rows, \@extra);
	#pArrArr(\@rows);
	#push(@rows, \@zero);
	my $a = pdl[\@rows];
#	print $a;
	my $inv = inv($a);
#	print $inv;
	my @row = (0) x (scalar(@first) - 1);
	push(@row, 1);
	my $r = pdl[\@row];
	my $target = $r->transpose;
#	print $target;
	my $res = $inv x $target;
	my @res = $res->list;
#	pArr \@res;
	return \@res;
	#my $b = $a->transpose;
	#print $a;
	#print "\n";
	#my $zero = vzeroes(scalar(@first));
	#print $zero;
	#my $sol = lu_backsub(lu_decomp($a), $zero);
	
	#my $sol = $a->solve;
	#my @normal;
	#for my $i (0..(scalar(@first) - 1)){
	#	push(@normal, $sol->[$i]->[0]);
	#}
	#return \@normal

}

#usage: candidatePole($diagram, $facet)
#facets needs to actually be a facet
#returns the candidate pole as a float
#need to be careful if diagram isn't reduced
#facet needs to be simplicial
sub candidatePole{
	my $diagram = shift;
	my $facet = shift;
	my @vertices;
	for my $index (@{$facet}){
		push(@vertices, $diagram->[$index]);
	}
	my $normal = normal(\@vertices);
	my $nu = sumArray($normal);
	my $N = 0;
	for my $index (0..(scalar(@{$normal}) - 1)){
		$N += ($vertices[0]->[$index])*($normal->[$index]);
	}
	my $candidate = -$nu/$N;
	return $candidate;
}


#usage: allCandidatePoles(diagram)
#diagram should be completely reduced
#returns an arref of all candidate poles 
#diagram does not need to be simplicial
#list includes multiplicity
#does not round
sub allCandidatePoles{
	my $diagram = shift;
	my @candidates;
	my $subdiv = nonSimpDiagramToSimp($diagram);
	my @flist = @{$subdiv->FACETS};
	my $perturbed = diagramToPerturbedSubdiv($diagram);
	for my $facet (@flist){
		my @f = @{$facet};
		my $tri = findTriangulated($diagram, $perturbed, \@f)->[0];
		push(@candidates, candidatePole($diagram, $tri));	
	}
	return \@candidates;

}


#usage: allTriangulations($diagram, $iter)
#generates $iter random triangulations of a non-simplicial diagram
#returns a list of the unique triangulations
#only checks if they are combinatorially isomorphic, not isomorphic as subdivisions
sub allTriangulations{
	my $diagram = shift;
	my $iter = shift;
	my @uniques;
	for my $i (0..($iter - 1)){
		my $unique = 1;
		my $perturbed = diagramToPerturbedSubdiv($diagram);
		for my $subdiv (@uniques){
			if (isomorphic($subdiv, $perturbed)){
				$unique = 0;
				last;
			}
		}
		if ($unique == 1){
			push(@uniques, $perturbed);
		}
	}
	return \@uniques;
}
#usage: toReverseProjective(aref)
#adds a 1 to the start of the array
#interpret as projectivizing the point
sub toReverseProjective{
	my $aref = shift;
	my @array = @{$aref};
	my @one = (1);
	push(@one, @array);
	return \@one;
}


#usage: toProjectiveArray($AoA)
#takes an arref of arrefs
#interprets as an array of points
#projectivizes them by adding 1 to start of each coord
sub toReverseProjectiveArray{
	my $aref = shift;
	my @array = @{$aref};
	my @proj = map(toReverseProjective($_), @array);
	return \@proj;
}

#usage: returnLatticePoints($diagram, $face)
#returns all lattice points in the interior of the box of that face
sub returnLatticePoints{
	my @diagram = @{shift @_};
	my $face = shift;
	my @verts; 
	my $num = scalar(@{$face});
	my $dim = scalar(@{$diagram[0]});
	my $indices = [0..($num - 1)];
	my @subsets = subsets($indices);
	for my $subset (@subsets){
		my @point = (0) x $dim;
		for my $index (@{$subset}){
			for my $i (0..($dim - 1)){
				$point[$i] += $diagram[$face->[$index]]->[$i];
			}
		}
		push(@verts, \@point);
	}
	#forms the polytopes
	my $proj = toReverseProjectiveArray(\@verts);
	#my $mat = new Matrix<Rational>($proj);
	my $poly = new Polytope<Rational>(POINTS=>$proj);
	#return $poly;
	my @lattice = @{$poly->INTERIOR_LATTICE_POINTS};
	my @pointlist = map(vectorToArray($_), @lattice);
	#turns back into array and deprojectizes
	map(splice(@{$_}, 0, 1), @pointlist);
	return \@pointlist;
}


#getFacetList($diagram)
#returns the list of facets in AoA format
#needs to be simplicial 
sub getFacetList{
	my $diagram = shift;
	my $simp = diagramToSubdiv($diagram);
	my @fs = @{$simp->FACETS};
	@fs = map(vectorToArray($_), @fs);
	return \@fs;
}

#computeWeight($diagram, $face, $facet containg face, $lattice point interior of box of the face)
#computes the sum of the coefficients expressing that lattice point as a linear combination of vertices of face
#used for computing weighted l^* polynomial
#doesn't actually need the face
sub computeWeight{
	my $diagram = shift;
	my $face = shift;
	my $facet = shift;
	my $point = shift;
	my $numvert = scalar(@{$facet}) - 1;
	#creates AoA of the coordinants of of P
	my @coords = ();
	for my $i (0..$numvert){
		push(@coords, $diagram->[$facet->[$i]]);
	}
	#solves linear equation

	my @row = @{$point};
	my $r = pdl[\@row];
	my $target = $r->transpose;
	#now creates the matrix of the coords
	my $tpose = pdl[\@coords];
	my $mat = $tpose->transpose;
	my $inv = inv($mat);
	my $res = $inv x $target;
	my @res = $res->list;
	return canonicalMod1(sumArray(\@res));
}

#usage: canonicalMod1(number)
#finds a representative of the number mod 1 that is between 0 and 1
sub canonicalMod1{
	my $num = shift;
	$num = $num - int($num);
	if ($num < 0){
		$num += 1;
	}
	return $num;
}

#usage: returnFaceFacet($subdiv)
#returns all faces in the form of [face, facet that contains the face]
#facet that contains the face is ar
sub returnFaceFacet{
	my $subdiv = shift;
	my @fs = @{$subdiv->FACETS};
	@fs = map(vectorToArray($_), @fs);
	#use hash to find unique faces
	my %hash;
	my @pairs;
	for my $facet (@fs){
		my @faces = subsets($facet);
		for my $face (@faces){
			my $str = "@{$face}";
			if (not $hash{$str}){
				$hash{$str} = 1;
				push(@pairs, [$face, $facet]);
			}
		}
	}
	return \@pairs;

}

#usage: latticePointToArray(lattice point)
#turns a lattice point into an array
sub latticePointToArray{
	my $lattice = shift;
	my @converted;
	for my $val(@{$lattice}){
		push(@converted, "$val");
	}
	return \@converted;
}

#usage: ellStar($diagram, $face, $facet containing face)
#returns an array giving the coefficients of ellStar of that face evaluated at 1
sub ellStar{
	my $diagram = shift;
	my $face = shift;
	my $facet = shift;
	my $lattice = returnLatticePoints($diagram, $face);
	my @lattice = map(latticePointToArray($_), @{$lattice});
	my %hash;
	for my $point(@lattice){
		my $a = computeWeight($diagram, $face, $facet, $point);
		if (exists($hash{$a})){
			$hash{$a} += 1;
		}
		else{
			$hash{$a} = 1;
		}
	}
	my @results;
	for my $key (keys %hash){
		push(@results, [$key, $hash{$key}]);
	}
	return \@results;
}

#usage: findLatticePoints($diagram, $face, $facet containing face, $number mod 1)
#returns all lattice points in the box of that face such that in ell^* term is the number mod 1
sub findLatticePoints{
	my $diagram = shift;
	my $face = shift;
	my $facet = shift;
	my $number = shift;
	my @listofpoints;
	my $lattice = returnLatticePoints($diagram, $face);
	my @lattice = map(latticePointToArray($_), @{$lattice});
	for my $point(@lattice){
		my $a = computeWeight($diagram, $face, $facet, $point);
		#allows some numerical imprecision
		if (abs($a - $number) < 0.0000001){
			push(@listofpoints, $point);
		}
	}

	return \@listofpoints;

}

#usage: linearExpression($diagram, $facet, $point)
#facet must be simplicial
#expresses the point as a linear combination of the vertices in the facet
sub linearExpression{
	my $diagram = shift;
	my $facet = shift;
	my $point = shift;
	my $numvert = scalar(@{$facet}) - 1;
	#creates AoA of the coordinants of of P
	my @coords = ();
	for my $i (0..$numvert){
		push(@coords, $diagram->[$facet->[$i]]);
	}
	#solves linear equation

	my @row = @{$point};
	my $r = pdl[\@row];
	my $target = $r->transpose;
	#now creates the matrix of the coords
	my $tpose = pdl[\@coords];
	my $mat = $tpose->transpose;
	my $inv = inv($mat);
	my $res = $inv x $target;
	my @res = $res->list;
	return \@res;
}

#usage: minCritFace($diagram, $facet)
#returns the minimal critical face contained in the facet
#i.e., returns the minimal face whose affine span intersects the ray spanned by (1,...,1)
#diagram must be reduced
sub minCritFace{
	my $diagram = shift;
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
	my @crit = ();
	my @res = $res->list;
	for my $j (0..$dim){
		if (abs($res[$j]) > 0.00000001){
			push(@crit, $facet->[$j]);
		}
	}
	return \@crit;
}

#usage: returnPeak($diagram, $face, coordinate)
#check if the face is B_1 in that coordinate
#if it is, returns the peak
#if it is not, returns -1
sub returnPeak{
	my $diagram = shift;
	my @face = @{shift @_};
	my $coordinate = shift;
	my $peak = -1;
	for my $vertex (@face){
		if ($diagram->[$vertex]->[$coordinate] > 1){
			return -1;
		}

		if ($diagram->[$vertex]->[$coordinate] == 1){
			if ($peak == -1){
				$peak = $vertex;
			}
			else{
				return -1;
			}
		}
	}	
	return $peak;
}

#usage: returnRelativePeak($diagram, $face, coordinate)
#check if the face is B_1 in that coordinate
#if it is, returns the relative position of the peak in the face
#if it is not, returns -1
sub returnRelativePeak{
	my $diagram = shift;
	my @face = @{shift @_};
	my $numvert = scalar(@face);
	my $coordinate = shift;
	my $peak = -1;
	for my $i (0..($numvert - 1)){
		if ($diagram->[$face[$i]]->[$coordinate] > 1){
			return -1;
		}

		if ($diagram->[$face[$i]]->[$coordinate] == 1){
			if ($peak == -1){
				$peak = $i;
			}
			else{
				return -1;
			}
		}
	}	
	return $peak;
}

#usage: faceType($diagram, $face)
#takes a face that should be a critical facet to be interesting
#Finds all directions that this face is B_1 in
#arranges them based on which vertex is the peak
#returns an array of the number of vertices that each peak is B_1 in, sorted
#returns 0 if it is not a B_1 face
sub faceType{
	my $diagram = shift;
	my @face = @{shift @_};
	my $numvert = scalar(@face);
	my $dim = scalar(@{$diagram->[0]});
	my @peaks = (0) x ($numvert);
	for my $i (0..($dim - 1)){
		if (returnRelativePeak($diagram, \@face, $i) > -1){
			$peaks[returnRelativePeak($diagram, \@face, $i)] += 1;
		}
	}
	#sorts and removes 0's
	my @type = sort {$b <=> $a} @peaks;
	if ($type[0] == 0){
		return 0;
	}
	for my $i (0..($numvert -1)){
		if($type[$numvert - 1 - $i] == 0){
			pop(@type);
		}
		else{
			return \@type;
		}
	}

}

#usage: hasGoodType($diagram, $face)
#check if the face is B_1 face and has good type, i.e. all entries at least 2
#returns 1 if it has good type, 0 otherwise
sub hasGoodType{
	my $diagram = shift;
	my $face = shift;
	my $type = faceType($diagram, $face);
	if ($type == 0){
		return 0;
	}
	my $num = scalar(@{$type});
	if ($type->[$num - 1] > 1){
		return 1;
	}
	return 0;
}

#usage: lookForGoodType($diagram, $subdiv)
#check if the essential face of any of the B_1 facets has good type
#returns 0 if none of them have good type
#returns an AoA of the faces that do have good type
sub lookForGoodType{
	my $diagram = shift;
	my $subdiv = shift;
	my @B1s = @{returnB1Facets($diagram, $subdiv)};
	my @good;
	for my $facet (@B1s){
		my $crit = minCritFace($diagram, $facet);
		if (hasGoodType($diagram, $crit)){
			push(@good, $crit);
		}
	}
	if (scalar(@good) == 0){
		return 0;
	}
	return removeDuplicates(\@good);
}



#usage: findFacet($simplicial complex, $face)
#finds a facet containing that face
#if it isn't a face, returns 0
sub findFacet{
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
					return $facet;
				}
			}
		}

	}
	return 0;
}




#usage: allBigFaces($subdiv, $size)
#generates all faces that have at least $size vertices
sub allBigFaces{
	my $subdiv = shift;
	my $size = shift;
	my @fs = @{$subdiv->FACETS};
	@fs = map(vectorToArray($_), @fs);
	#use hash to find unique faces
	my %hash;
	my @allfaces;
	for my $facet (@fs){
		my @faces = subsets($facet);
		for my $face (@faces){
			if (scalar(@{$face}) < $size){
				next;
			}
			my $str = "@{$face}";
			if (not $hash{$str}){
				$hash{$str} = 1;
				push(@allfaces, $face);
			}
		}
	}
	return \@allfaces;

}

#usage: allFacesSize($subdiv, $size)
#generates all faces that have exactly $size vertices
sub allFacesSize{
	my $subdiv = shift;
	my $size = shift;
	my @fs = @{$subdiv->FACETS};
	@fs = map(vectorToArray($_), @fs);
	#use hash to find unique faces
	my %hash;
	my @allfaces;
	for my $facet (@fs){
		my @faces = subsets($facet, $size);
		for my $face (@faces){
			my $str = "@{$face}";
			if (not $hash{$str}){
				$hash{$str} = 1;
				push(@allfaces, $face);
			}
		}
	}
	return \@allfaces;

}




#use: hasFullParition($subdiv)
#checks if any facet has a full partition with P empty
#returns 1 if it does, 0 if it does not
#works with E = emptyset
sub hasFullPartitionPEmpty{
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
					return 1;
				}
			}
		}
	}
	return 0;
}




#usage: specialLSOP(subdiv)
#assumes E = \emptyset 
#generates an AoA, (dim subdiv) x (number of vertices)
#the ith spot is the coefficients of the a l.s.o.p. for the subdiv
sub specialLSOP{
	my $subdiv = shift;
	my $dim = $subdiv->DIM;
	my $nverts = $subdiv->N_VERTICES;
	my @answer;
	for my $i (0..$dim){
		my @piece = (0) x $nverts;
		for my $v (0..$nverts - 1){
			if ((($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$v]])->[$i]) > 0){
				$piece[$v] = rand();
			}
		}
		push(@answer, \@piece);
	}
	return \@answer;
}

#usage: rankPDL(PDL matrix)
#returns rank of a matrix
#uses SVD 
#doesn't work for the 0 matrix 
sub rankPDL{
	my $pdlmat = shift;
	my @d = $pdlmat->dims;
	if (($d[0] == 1) or ($d[1] == 1)){
		return 1;
	}
	if ($d[0] > $d[1]){
		$pdlmat = $pdlmat->transpose;
	}
	my ($u, $s, $v) = svd($pdlmat);
	my @sings = $s->list;
	my $rank = 0;
	for my $i (0..(scalar(@sings) - 1)){
		if (abs($sings[$i]) > 0.0000001){
			$rank += 1;
		}
	}
	return $rank;
}

#use: allIntFaces($subdiv, $size, $subset of vertices)
#finds all interior faces supported on the given subset of vertices of a given size
sub allIntFaces{
	my $subdiv = shift;
	my $size = shift;
	my $subset = shift;
	my @fs = @{$subdiv->FACETS};
	@fs = map(vectorToArray($_), @fs);
	#use hash to finds all faces
	my %hash;
	my @allfaces;
	for my $facet (@fs){
		my @faces = subsets($facet, $size);
		for my $face (@faces){
			my $str = "@{$face}";
			if (not $hash{$str}){
				$hash{$str} = 1;
				push(@allfaces, $face);
			}
		}
	}
	my @goodfaces;
	for my $face (@allfaces){
		if (scalar(@{carrier($subdiv, $face)}) > 0){
			next;
		}
		my $lc = List::Compare->new($face, $subset);
		if (scalar($lc->get_intersection) == $size){
			push(@goodfaces, $face);
		}
	}
	return @goodfaces;
}

#use: allCD1faces($subdiv, $size, $subset of vertices)
#finds all carrier codimension 1 supported on the given subset of vertices of a given size
sub allCD1Faces{
	my $subdiv = shift;
	my $size = shift;
	my $subset = shift;
	my @fs = @{$subdiv->FACETS};
	@fs = map(vectorToArray($_), @fs);
	#use hash to finds all faces
	my %hash;
	my @allfaces;
	for my $facet (@fs){
		my @faces = subsets($facet, $size);
		for my $face (@faces){
			my $str = "@{$face}";
			if (not $hash{$str}){
				$hash{$str} = 1;
				push(@allfaces, $face);
			}
		}
	}
	my @goodfaces;
	for my $face (@allfaces){
		if (scalar(@{carrier($subdiv, $face)}) != 1){
			next;
		}
		my $lc = List::Compare->new($face, $subset);
		if (scalar($lc->get_intersection) == $size){
			push(@goodfaces, $face);
		}
	}
	return @goodfaces;
}

#usage: monomialVanishes($subdiv, minimal interior face, array of vertices)
#checks if the monomial is 0 in the local face module restricted to the subcomplex induced by these vertices
#face needs to be given in increasing order
#returns 0 if it vanishes 
#returns 1 if it does not vanish
sub monomialVanishes{
	my $subdiv = shift;
	my $face = shift;
	my $size = scalar(@{$face});
	my $subset = shift;
	my $lsop = specialLSOP($subdiv);
	my @cd1faces = allCD1Faces($subdiv, $size - 1, $subset);
	my @intfaces = allIntFaces($subdiv, $size, $subset);
	#special case when no cd1 faces
	if (scalar(@cd1faces) == 0){
		return 1;
	}
	my $numint = scalar(@intfaces);
	my @columns = ();
	for my $cd1face (@cd1faces){
		my $missing = carrier($subdiv, $cd1face)->[0];
		my @facecolumn = (0) x $numint;
		for my $i (0..($numint - 1)){
			my $lc = List::Compare->new($cd1face, $intfaces[$i]);
			my @others = $lc->get_complement;
			if (scalar(@others) > 1){
				next;
			}
			$facecolumn[$i] = $lsop->[$missing]->[$others[0]];
		}
		push(@columns, \@facecolumn);
	}
	my $mat = pdl(\@columns);
	my $initrank = rankPDL($mat);
	my @testcolumn = (0) x $numint;
	#finds the location in @intfaces corresponding to the chosen face 
	for my $i (0.. ($numint - 1)){
		if (entrywiseEquality($face, $intfaces[$i])){
			$testcolumn[$i] = 1;
			last;
		}
	}
	push(@columns, \@testcolumn);
	my $mat2 = pdl(\@columns);
	if (rankPDL($mat2) == 1 + $initrank){
		return 1;
	}
	return 0;
}




#usage: computeVw(subdiv, face, vertex)
#computes |V_w|, finds all in which the face is a pyramid with apex w 
#returns the number |V_w|
#vertex should be in face
sub computeVw{
	my $subdiv = shift;
	my $face = shift;
	my $vertex = shift;
	my $Vw = 0;
	for my $i (0..$subdiv->DIM){
		if ($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$vertex]]->[$i] == 0){
			next;
		}
		my $numnonzero = 0;
		for my $v (@{$face}){
			if ($subdiv->COORDINATES->[$subdiv->VERTEX_INDICES->[$v]]->[$i] > 0){
				$numnonzero += 1;
			}

		}
		if ($numnonzero == 1){
			$Vw += 1;
		}
	}
	return $Vw;

}

#usage: hasInteriorPartition($subdiv)
#checks if the subdivisions has an interior partition with E empty and each |V_w| > 1 for w in P
#slow
#returns 0 if it does not
#returns the partition if it does
sub hasInteriorPartition{
	my $subdiv = shift;
	#first does the case P = \emptyset
	my @facets = @{$subdiv->FACETS};
	my @face = ();
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
					return [$split, \@other];
				}
			}
		}
	}
	my $bad = 0;
	my $d = $subdiv->DIM;
	my $maxP =  int(($d+ 1)/2);
	for my $Psize (1..$maxP){
	#	#loops over possible P
		my @Pcandidates = @{allFacesSize($subdiv, $Psize)};
		for my $P (@Pcandidates){
			$bad = 0;
			#first checks if they have a chance of being a good P 

			for my $v (@{$P}){
				my $vW = computeVw($subdiv, $P, $v);
				if (($vW < 2) or ($d < 2*$Psize + $vW - 3)){
					$bad = 1;
					last;
				}
			}
			if ($bad == 1){
				next;
			}
			#loops over faces of link, looking for interior partitions with the given P 
			#creates a list of all faces of the link, will be a bit inefficient 
			my $link = new topaz::GeometricSimplicialComplex(topaz::link_complex($subdiv, $P));
			my $diagram = $link->HASSE_DIAGRAM;
		    my @face_list = @{$diagram->FACES};
		    shift(@face_list);
		    my @face_list2 = map(reindex($link, vectorToArray($_)), @face_list);
		    for my $face (@face_list2){
		    	$bad = 0;
		    	my $F2 = union($face, $P);
				my @F = sort {$a <=> $b} @{$F2};
		    	#checks if interior 
		    	if (scalar(@{carrier($subdiv, \@F)}) > 0){
		    		next;
		    	}

		    	#checks if the condition on P still holds 

				for my $v (@{$P}){
					if (computeVw($subdiv, \@F, $v) < 2){
						$bad = 1;
					last;
					}
				}
				if ($bad == 1){
					next;
				}
				#tries to subdivide $face into F_1, F_2, s.t. F_1 \cup P, F_2 \cup P both interior

				for my $l (0..(int(scalar(@{$face})/2))){
					my @divisions = subsets($face, $l);
					for my $split (@divisions){
						if (scalar(@{carrier($subdiv, union($split, $P))}) > 0){
							next;
						}
					my $list = List::Compare->new($face, $split);
					my @other = $list->get_unique;
						if (scalar(@{carrier($subdiv, union($P, \@other))}) == 0){
							return [$split, \@other, $P];
						}
					}
				}

		    }
		}
	}
	return 0;
}




#usage: sortIntoClusters($diagram, list of facets)
#list of facets should be a list of facets all contributing the same candidate pole 
#sorts the facets by into clusters based on the minimal face contributing the candidate pole 
#should be simplicial (for now)
#returns an array of centers, follow by an AoAoA of facets with a given center 
sub sortIntoClusters{
	my $diagram = shift;
	my $listOfFacets = shift;
	my @centers;
	my @clusters;
	for my $facet (@{$listOfFacets}){
		my $new = 1;
		my @facet = @{$facet};
		my $essential = minCritFace($diagram, \@facet);
		for my $i (0..(scalar(@centers) - 1)){
			if (entrywiseEquality($essential, $centers[$i])){
				push(@{$clusters[$i]}, \@facet);
				$new = 0;
				next;
			}
		}
		if ($new == 1){
			push(@centers, $essential);
			push(@clusters, [\@facet]);
		}
	}
	return [\@centers, \@clusters];

}

#usage: allContributingCandidatePole($diagram, $list of facets, rational number)
#returns an AoA of all the facets contributing the given rational number 
sub allContributingCandidatePole{
	my $diagram = shift;
	my @facets = @{shift @_};
	my $candidate = shift;
	my @contributingfacets;
	for my $index (0..(scalar(@facets) - 1)){
		my $f = $facets[$index];
		if ($candidate == rationalCandidatePole($diagram, $f)){
			push(@contributingfacets, $f);
		}
	}
	return \@contributingfacets;

}

#usage: checkIfCoherent($diagram, cluster of facets)
#given a cluster of facets all sharing the same minimal critical face,
#checks if there is a way to choose an apex and a base for all the facets 
#so that if two of the facets intersect and have the same apex, then they have the same base 
#does this by looping over all possible choices of the apex, base
#returns the choice if there is a coherent choice 
#returns 0 otherwise 
sub checkIfCoherent{
	my $diagram = shift;
	my $cluster = shift;
	my $dim = scalar(@{$diagram->[0]});
	my $num = scalar(@{$cluster});
	my @listofpairs = map(peakDirectionPairs($diagram, $_), @{$cluster});
	my $toTry = cartesian_product(@listofpairs);
	for my $arrangement (@{$toTry}){
		my $bad = 0;
		for my $f1 (0..($num - 1)){
			if ($bad == 1){
				last;
			}
			for my $f2 (0..($num - 1)){
				if ($f1 == $f2){
					next;
				}
				my @facet1 = @{$cluster->[$f1]};
				my @facet2 = @{$cluster->[$f2]};
				my $lc = List::Compare->new((\@facet1, \@facet2));
				if (scalar($lc->get_intersection) < ($dim - 1)){
					next;
				}
				my $choice1 = $arrangement->[$f1];
				my $choice2 = $arrangement->[$f2];
				if ($choice1->[0] == $choice2->[0]){
					if ($choice1->[1] != $choice2->[1]){
						$bad = 1;
						last;
					}
				}
			}

		}
		if ($bad == 0){
			return $arrangement
		}
	}
	return 0;
}

#usage: peakDirectionPairs($diagram, $facet)
#returns 0 if the facet is not B_1
#returns all pairs of a peak of the B_1 facet and a direction that it is B_1 in.
#pair is [vertex, direction]
#works with any face, doesn't have to be a facet
sub peakDirectionPairs{
	my $diagram = shift;
	my $facet = shift;
	my @pairs;
	for my $i (0..(scalar(@{$diagram->[0]}) - 1)){
		my $P;
		my $sum = 0;
		for my $v (@{$facet}){
			if ($diagram->[$v]->[$i] > 1){
				$sum = 2;
				last;
			}
			if ($diagram->[$v]->[$i] == 1){
				$P = $v;
				$sum += 1;
			}
			if ($sum > 1){
				last;
			}
		}
		if ($sum == 1){
			push(@pairs, [$P, $i]);
		}
	}
	return \@pairs;
}

#usage: exactNormal(AoA)
#take an array of a bunch of vertices 
#returns a normal vector 
#only looks at the first n vectors
#returns it as a polymake rational 
#may fail if not simplicial. 
sub exactNormal{
	my $vectors = shift;
	my @rows;
	my @first = @{$vectors->[0]};
	for my $i (1..(scalar(@first) - 1)){
		my @row;
		for my $j (0..(scalar(@first) - 1)){
			push(@row, $first[$j] - $vectors->[$i]->[$j])
		}
		#push(@row, 0);
		push(@rows, \@row);
	}
	#pads matrix with an extra row to determine the system and hopefully get integral coefficients
	my @extra = (1) x (scalar(@first));
	push(@rows, \@extra);
	my $a = new Matrix<Rational>(\@rows);
	my @row = (0) x (scalar(@first) - 1);
	push(@row, 1);
	my $v = new Vector<Rational>(\@row);
	my $res = lin_solve($a, $v);
	return $res;


}

#usage: rationalCandidatePole($diagram, $facet)
#facets needs to actually be a facet
#returns the candidate pole as a float
#need to be careful if diagram isn't reduced
#facet needs to be simplicial
sub rationalCandidatePole{
	my $diagram = shift;
	my $facet = shift;
	my @vertices;
	for my $index (@{$facet}){
		push(@vertices, $diagram->[$index]);
	}
	my $normal = exactNormal(\@vertices);
	my $nu = sumArray($normal);
	my $N = 0;
	for my $index (0..(scalar(@{$normal}) - 1)){
		$N += ($vertices[0]->[$index])*($normal->[$index]);
	}
	my $candidate = new Rational(-$nu/$N);
	return $candidate;
}

#returnUniqueApex($diagram, $face)
#returns all vertices that are a unique apex 
#i.e., apices that are apices in a unique direction
sub returnUniqueApex{
	my $diagram = shift;
	my $face = shift;
	my $peaksPairs = peakDirectionPairs($diagram, $face);
	my $num = scalar(@{$peaksPairs}) - 1;
	if ($num == -1){
		return [];
	}
	if ($num == 0){
		return [$peaksPairs->[0]->[0]];
	}
	my @peaks;
	for my $pair (@{$peaksPairs}){
		push(@peaks, $pair->[0]);
	}
	my @uniq = do {
    	my %count;
    	$count{$_}++ for @peaks;
    	grep {$count{$_} == 1} keys %count;
	};

	return \@uniq;

}
#usage: hasFakeUniqueApex($diagram, [$center, $facets])
#takes in a cluster of facets with a common center 
#returns 1 if there is a vertex of the center that is an apex in a unique direction of the center 
#but is not an apex of any of the facets 
#a little inefficient, should only generate peakDirectionPairs once for each facet 
sub hasFakeUniqueApex{
	my $diagram = shift;
	my $clusterdata = shift;
	my $center = $clusterdata->[0];
	my $facets = $clusterdata->[1];
	my @fakes;
	my $uniques = returnUniqueApex($diagram, $center);
	for my $apex (@{$uniques}){
		my $bad = 0;
		for my $f (@{$facets}){
			if ($bad == 1){
				last;
			}
			my @peaks = @{peakDirectionPairs($diagram, $f)};
			for my $pair (@peaks){
				if ($pair->[0] == $apex){
					$bad = 1;
				}
			}
		}
		if ($bad == 0){
			push(@fakes, $apex);
		}
	}
	return \@fakes;
}

#usage: isELTCoherent($diagram, cluster of facets)
#given a cluster of facets all sharing the same minimal critical face,
#checks if there is a way to choose an apex and a base for all the facets 
#so that if two of the facets intersect, then they have the same base direction  
#returns 0 if it is not [ELT] coherent 
#returns the arrangement if it is [ELT] coherent
sub isELTCoherent{
	my $diagram = shift;
	my $cluster = shift;
	my $dim = scalar(@{$diagram->[0]});
	my $num = scalar(@{$cluster});
	my @listofpairs = map(peakDirectionPairs($diagram, $_), @{$cluster});
	my $toTry = cartesian_product(@listofpairs);
	for my $arrangement (@{$toTry}){
		my $bad = 0;
		for my $f1 (0..($num - 1)){
			if ($bad == 1){
				last;
			}
			for my $f2 (0..($num - 1)){
				if ($f1 == $f2){
					next;
				}
				my @facet1 = @{$cluster->[$f1]};
				my @facet2 = @{$cluster->[$f2]};
				my $lc = List::Compare->new((\@facet1, \@facet2));
				if (scalar($lc->get_intersection) < ($dim - 1)){
					next;
				}
				my $choice1 = $arrangement->[$f1];
				my $choice2 = $arrangement->[$f2];
				if ($choice1->[1] != $choice2->[1]){
					$bad = 1;
					last;
					
				}
			}

		}
		if ($bad == 0){
			return $arrangement
		}
	}
	return 0;

}



#usage:getAllClusterFaces($subdiv, $center)
#returns a list of all faces in the cluster 
#in other words finds all the faces in the star of a face
sub getAllClusterFaces{
	my $subdiv = shift;
	my $dim = $subdiv->DIM;
	my $center = shift;
	if (scalar(@{$center}) == 1 + $dim){
		return [$center];
	}
	my $link = new topaz::GeometricSimplicialComplex(topaz::link_complex($subdiv, $center));
    #creates array of the faces
    my $diagram = $link->HASSE_DIAGRAM;
    my $face_list = $diagram->FACES;
    my @face_list = @{$face_list};
    shift(@face_list);
    my @face_list2 = map(vectorToArray($_), @face_list);
    my @face_list3 = map(reindex($link, $_), @face_list2);
    for my $face (@face_list3){
    	push(@{$face}, @{$center});
    	@{$face} = sort {$a <=> $b} @{$face};

    }
    return \@face_list3;
}

#usage: checkIfOperative($diagram, $subdiv, $center)
#checks if there is an operative labeling of the poset of faces above the cluster 
#assumes simplicial
#returns 1 if there is an operative labeling, 0 otherwise
sub checkIfOperative{
	my $diagram = shift;
	my $subdiv = shift;
	my $center = shift;
	my @clusterfaces = @{getAllClusterFaces($subdiv, $center)};
	for my $face (@clusterfaces){
		if (scalar(@{returnUniqueApex($diagram, $face)}) == 0){
			return 0;
		}
	}
	return 1;
}

#sub: findLargeCDOperative($diagram)
#returns 1 if there is a cluster with center having codimension at least 2
#that has an operative labeling
sub findLargeCDOperative{
	my $diagram = shift;
	my $dim = scalar(@{$diagram->[0]});
	my $subdiv = diagramToSubdiv($diagram);
	my @allfacets = @{$subdiv->FACETS};
	my $centerclusters = sortIntoClusters($diagram, \@allfacets);
	my @centers = @{$centerclusters->[0]};
	for my $c (@centers){
		if (scalar(@{$c}) > $dim - 2){
			next;
		}
		if (checkIfOperative($diagram, $subdiv, $c)){
			pArr($c);
			return 1;
		}
	}
	return 0;
}

#usage: inHasse($hasse diagram, $face)
#takes hasse diagram of a polytope
#returns 1 if $face is a face 
#returns 0 others 
sub inHasse{
	my $hasse = shift;
	my $face = shift;
	for my $f (@{$hasse->FACES}){
		if (entrywiseEquality($face, \@{$f})){
			return 1;
		}
	}
	return 0;
}

#usage: subdivHasOperative(diagram, triangulation, candidate pole)
#candidate pole should be rational number 
#returns 1 if there is an operative labeling for the candidate pole 
#returns 0 otherwise
sub subdivHasOperative{
	my $diagram = shift;
	my $tri = shift;
	my $cand = shift;
	my @facets = @{$tri->FACETS};
	#finds facets with candidate pole s_0 
	my @contributing;
	for my $f (@facets){
		if (rationalCandidatePole($diagram, $f) == $cand){
			push(@contributing, $f);
		}
	}
	#gets the minimal faces 
	my $clusters = sortIntoClusters($diagram, \@contributing);
	for my $c (@{$clusters}){
		my $allfaces = getAllClusterFaces($tri, $c->[0]);
		for my $face (@{$allfaces}){
			if (scalar(@{returnUniqueApex($diagram, $face)}) == 0){
				return 0;
			}
		}
	}
	return 1;
}

#usage: checkIndependenceConjecture(diagram, candidate)
#generates a bunch of triangulations 
#checks the conjecture that whether they have an operative labeling is independent of triangulation 
#cand should be a rational number 
sub checkIndependenceConjecture{
	my $diagram = shift;
	my $cand = shift;
	my $tally = 0;
	for my $i (0..9){
		my $nonSimp = nonSimpDiagramToSimp($diagram);
		$tally += subdivHasOperative($diagram, $nonSimp, $cand);
	}
	if ($tally == 0 or $tally == 10){
		return 1;
	}
	print "Found counterexample";
	return 0;
}



















