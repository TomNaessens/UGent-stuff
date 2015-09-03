BioComp--HW3
============

install unipept
---------------

gem install --user-install unipept

decompose protein into peptides having length between 5 and 50
--------------------------------------------------------------

echo ${protein} | prot2pept | pept2filter

project steps (I guess)
-----------------------

- download the protein sequences of the 12 samples ( Predicted CDS (FASTA))
  https://www.ebi.ac.uk/metagenomics/projects/ERP001038
 
- compute the "metapeptidome" of each sample: the set of all peptides sequenced from the sample

- compute the intersection of the metapeptidomes of all positive samples (e.g. formula-fed babies)

- subtract from the intersection all peptides in the metapeptidomes of the samples in the negative
  set (e.g. breast-fed babies)
  
- try to find more information about the peptides in the "unique metapeptidome"
	- how many are there ?
	- what organisms do they come from (unipept pept2lca) ?
	- what biological functions are they involved in ?
	- you can also switch the rols of the positive and negative sets
