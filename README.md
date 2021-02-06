These are some functions that can be used to compute and study local h vectors using Polymake. The main files are Perl script that can be loaded into polymake. 

This was primarily written over the summer of 2019 while working on a project with Sam Payne related to local h vectors. It was originally based on some code written by Jason Schuchardt

There are three scripts. 

-- utilities.pl is a bunch of general Perl functions which have nothing to polymake 

-- subs.pl is a set of functions that can compute (relative) local h-vectors and do a lot of stuff with Newton polyhedra. 

-- localzeta.pl is code for compute the topological zeta function (of Denef and Loeser) of a Newton-nondegenerate polynomial. 


**Caution: the code may silently give wrong answers when computing with non-simplicial things. One should check very carefully. Often there is a version of a function that works for simplicial things, and another that works for non-simplicial things**
