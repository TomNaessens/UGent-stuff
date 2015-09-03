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
import joldespice.util.xml.converters.NodeConverter;
import org.jdom.Element;

public class PointNodeConverter implements NodeConverter<PointNode> {

	public PointNode importNode(Element e) {
		return new PointNode(new Point(
			   Integer.parseInt(e.getChild("xynode").getAttributeValue("x")),
			   Integer.parseInt(e.getChild("xynode").getAttributeValue("y"))));
	}

	public void exportNode(Element parent, PointNode n) {
		Element type = new Element("xynode");
		type.setAttribute("x", Integer.toString(n.getX()));
		type.setAttribute("y", Integer.toString(n.getY()));
		parent.addContent(type);
	}
}
