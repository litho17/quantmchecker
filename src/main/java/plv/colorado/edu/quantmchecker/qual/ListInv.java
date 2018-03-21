package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@SubtypeOf({InvTop.class})
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Documented
//Check these qualifiers: package org.checkerframework.framework.qual;
public @interface ListInv {
    //@JavaExpression
    public String[] value();
}