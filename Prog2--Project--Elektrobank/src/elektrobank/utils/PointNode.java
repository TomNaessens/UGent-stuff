/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.utils;

import java.awt.Point;
import joldespice.components.SimpleNode;

public class PointNode extends SimpleNode {

	Point pt = new Point();

	public PointNode(Point pt) {
		this.pt.setLocation(pt);
	}

	public void setLocation(Point pt) {
		this.pt.setLocation(pt);
	}

	public int getX() {
		return this.pt.x;
	}

	public int getY() {
		return this.pt.y;
	}

	public Point getLocation() {
		return pt;
	}

}
