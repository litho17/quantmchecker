/*
Copyright 2006 Jerry Huxtable

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/
package SnapBuddy_1.com.jhlabs.image;

import java.awt.*;
import java.awt.image.*;
import java.io.*;

public class FadeFilter extends PointFilter {

    private int width, height;

    private float angle = 0.0f;

    private float fadeStart = 1.0f;

    private float fadeWidth = 10.0f;

    private int sides;

    private boolean invert;

    private float m00 = 1.0f;

    private float m01 = 0.0f;

    private float m10 = 0.0f;

    private float m11 = 1.0f;

    /**
     * Specifies the angle of the texture.
     * @param angle the angle of the texture.
     * @angle
     * @see #getAngle
     */
    public void setAngle(float angle) {
        this.angle = angle;
        float cos = (float) Math.cos(angle);
        float sin = (float) Math.sin(angle);
        m00 = cos;
        m01 = sin;
        m10 = -sin;
        m11 = cos;
    }

    /**
     * Returns the angle of the texture.
     * @return the angle of the texture.
     * @see #setAngle
     */
    public float getAngle() {
        return angle;
    }

    public void setSides(int sides) {
        setSidesHelper(sides);
    }

    public int getSides() {
        return sides;
    }

    public void setFadeStart(float fadeStart) {
        setFadeStartHelper(fadeStart);
    }

    public float getFadeStart() {
        return fadeStart;
    }

    public void setFadeWidth(float fadeWidth) {
        setFadeWidthHelper(fadeWidth);
    }

    public float getFadeWidth() {
        return fadeWidth;
    }

    public void setInvert(boolean invert) {
        setInvertHelper(invert);
    }

    public boolean getInvert() {
        return invert;
    }

    public void setDimensions(int width, int height) {
        setDimensionsHelper(height, width);
    }

    public int filterRGB(int x, int y, int rgb) {
        float nx = m00 * x + m01 * y;
        float ny = m10 * x + m11 * y;
        int conditionObj0 = 2;
        int conditionObj1 = 3;
        if (sides == conditionObj0)
            nx = (float) Math.sqrt(nx * nx + ny * ny);
        else if (sides == conditionObj1)
            nx = ImageMath.mod(nx, 16);
        else if (sides == 4)
            nx = symmetry(nx, 16);
        int alpha = (int) (ImageMath.smoothStep(fadeStart, fadeStart + fadeWidth, nx) * 255);
        if (invert)
            alpha = 255 - alpha;
        return (alpha << 24) | (rgb & 0x00ffffff);
    }

    public float symmetry(float x, float b) {
        /*
		int d = (int)(x / b);
		x = ImageMath.mod(x, b);
		if ((d & 1) == 1)
			return b-x;
		return x;
*/
        x = ImageMath.mod(x, 2 * b);
        if (x > b)
            return 2 * b - x;
        return x;
    }

    /*
	public float star(float x, float y, int sides, float rMin, float rMax) {
		float sideAngle = 2*Math.PI / sides;
		float angle = Math.atan2(y, x);
		float r = Math.sqrt(x*x + y*y);
		float t = ImageMath.mod(angle, sideAngle) / sideAngle;
		if (t > 0.5)
			t = 1.0-t;
	}
*/
    public String toString() {
        return "Fade...";
    }

    private void setSidesHelper(int sides) {
        this.sides = sides;
    }

    private void setFadeStartHelper(float fadeStart) {
        this.fadeStart = fadeStart;
    }

    private void setFadeWidthHelper(float fadeWidth) {
        this.fadeWidth = fadeWidth;
    }

    private void setInvertHelper(boolean invert) {
        this.invert = invert;
    }

    private void setDimensionsHelper(int height, int width) {
        this.width = width;
        this.height = height;
        super.setDimensions(width, height);
    }
}
