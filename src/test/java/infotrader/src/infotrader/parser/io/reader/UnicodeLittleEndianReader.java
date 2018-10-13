/*
 * Copyright (c) 2009-2016 Matthew R. Harrah
 *
 * MIT License
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */
package infotrader.src.infotrader.parser.io.reader;

import java.io.IOException;
import java.io.InputStream;

import infotrader.src.infotrader.parser.exception.InfoTraderParserException;
import infotrader.src.infotrader.parser.parser.InfoTraderParser;

/**
 * A reader that loads from an input stream and gives back a collection of strings representing the data therein. This
 * implementation handles little-endian Unicode data.
 * 
 * @author frizbog
 */
final class UnicodeLittleEndianReader extends AbstractEncodingSpecificReader {

    /**
     * Are we at the end of file yet?
     */
    private boolean eof = false;

    /**
     * The line buffer for the current line
     */
    private final StringBuilder lineBuffer = new StringBuilder();

    /**
     * Constructor
     * 
     * @param parser
     *            the { InfoTraderParser} which is using this object to read files
     * 
     * @param byteStream
     *            the stream of data to be read
     */
    public UnicodeLittleEndianReader(InfoTraderParser parser, InputStream byteStream) {
        super(parser, byteStream);
    }

    @Override
    public String nextLine() throws IOException, InfoTraderParserException {
        String result = null;

        boolean beginningOfFile = true;

        while (!eof) {
            int currChar1 = byteStream.read();
            if (currChar1 >= 0) {
                bytesRead++;
            }
            int currChar2 = byteStream.read();
            if (currChar2 >= 0) {
                bytesRead++;
            }

            // Check for EOF
            if (currChar1 < 0 || currChar2 < 0) {
                // hit EOF - add final line buffer (last line) and get out
                if (lineBuffer.length() > 0) {
                    result = lineBuffer.toString();
                }
                eof = true;
                break;
            }

            // If it's a byte order marker at the beginning of the file, discard it
            if (beginningOfFile && (currChar1 == 0xFF && currChar2 == 0xFE)) {
                beginningOfFile = false;
                lineBuffer.setLength(0);
                break;
            }

            beginningOfFile = false;

            // Check for carriage returns or line feeds - signify EOL
            if ((currChar1 == 0x0D && currChar2 == 0x00) || (currChar1 == 0x0A && currChar2 == 0x00)) {
                if (lineBuffer.length() > 0) {
                    result = lineBuffer.toString();
                    lineBuffer.setLength(0);
                    break;
                }
                continue;
            }

            int unicodeChar = currChar2 << 8 | currChar1;
            lineBuffer.append(Character.valueOf((char) unicodeChar));
        }
        return result;
    }

    @Override
    void cleanUp() throws IOException {
        // do nothing
    }

}
