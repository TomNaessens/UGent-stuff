/*
 * Implementatie van een gewone rood-zwart boom die de kleuring van op p. 22 gebruikt
 * 
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree1 extends AbstractRBTree {
	
	@Override
	public void rebalance(MyVertex vertex) {
		standardRebalance(vertex);
	}
	
}
