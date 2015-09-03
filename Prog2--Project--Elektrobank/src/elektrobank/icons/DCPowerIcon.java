/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.icons;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import joldespice.components.linear.DCPower;

/**
 *
 * @author tnaessens
 */
public class DCPowerIcon extends IconPainter {

	public DCPowerIcon() {
		super(4);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c,g2,x,y);

		g2.drawLine(-2, -8, -2, 8);
		g2.drawLine(2, -4, 2, 4);
	}

	@Override
	public String getComponent() {
		return "DCPower";
	}
}
