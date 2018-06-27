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
// @Target({ElementType.LOCAL_VARIABLE, ElementType.FIELD, ElementType.PARAMETER, ElementType.METHOD})
//Check these qualifiers: package org.checkerframework.framework.qual;
public @interface Input {
    //@JavaExpression
    public String[] value();
}