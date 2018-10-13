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
package infotrader.src.infotrader.parser.parser;

import infotrader.src.infotrader.parser.model.Address;
import infotrader.src.infotrader.parser.model.StringTree;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;

/**
 * Parser for { Address} objects
 * 
 * @author frizbog
 *
 */
class AddressParser extends AbstractParser<Address> {


    AddressParser(InfoTraderParser InfoTraderParser, StringTree stringTree, Address loadInto) {
        super(InfoTraderParser, stringTree, loadInto);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    void parse() {
        if (stringTree.getValue() != null) {
            loadInto.getLines(true).add(stringTree.getValue());
        }
        if (stringTree.getChildren() != null) {
            for (StringTree ch : stringTree.getChildren()) {
                if (Tag.CITY.equalsText(ch.getTag())) {
                    loadInto.setCity(new StringWithCustomTags(ch));
                } else if (Tag.STATE.equalsText(ch.getTag())) {
                    loadInto.setStateProvince(new StringWithCustomTags(ch));
                } else if (Tag.POSTAL_CODE.equalsText(ch.getTag())) {
                    loadInto.setPostalCode(new StringWithCustomTags(ch));
                } else if (Tag.COUNTRY.equalsText(ch.getTag())) {
                    loadInto.setCountry(new StringWithCustomTags(ch));
                } else if (Tag.CONCATENATION.equalsText(ch.getTag())) {
                    if (loadInto.getLines(true).isEmpty()) {
                        loadInto.getLines().add(ch.getValue());
                    } else {
                        loadInto.getLines().set(loadInto.getLines().size() - 1, loadInto.getLines().get(loadInto.getLines().size() - 1) + ch.getValue());
                    }
                } else if (Tag.CONTINUATION.equalsText(ch.getTag())) {
                    loadInto.getLines(true).add(ch.getValue() == null ? "" : ch.getValue());
                } else {
                    unknownTag(ch, loadInto);
                }
            }
        }
    }

}
