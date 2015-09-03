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
import joldespice.components.nonlinear.Switch;

public class SwitchIcon extends IconPainter {

	boolean dicht;

	public SwitchIcon(boolean dicht) {
		super(20);
		this.dicht = dicht;
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c, g2, x, y);

		if (!dicht) {
			g2.drawLine(-10, -1, 10, -8);
		} else {
			g2.drawLine(-10, -1, 10, -1);
		}
	}

	@Override
	public String getComponent() {
		return "Switch";
	}

	public void setOpen(boolean bool) {
		dicht = bool;
	}
}
