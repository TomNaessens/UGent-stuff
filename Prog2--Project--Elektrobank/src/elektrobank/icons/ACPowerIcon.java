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
import joldespice.components.linear.ACPower;

public class ACPowerIcon extends IconPainter {

	public ACPowerIcon() {
		super(20);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();
		
		super.paintIcon(c,g2,x,y);

		g2.drawOval(-10, -10, 20, 20); // Ovaal
		g2.drawArc(-6, -3, 6, 6, 0, 180); // Halve cirkel links
		g2.drawArc(0, -3, 6, 6, 180, 180); // Halve cirkel rechts
	}

	@Override
	public String getComponent() {
		return "ACPower";
	}
}
