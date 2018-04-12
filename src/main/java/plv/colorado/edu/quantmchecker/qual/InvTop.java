package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.*;

/**
 * @author Tianhan Lu
 */
@DefaultQualifierInHierarchy
@InvisibleQualifier
// @DefaultFor({TypeUseLocation.UPPER_BOUND, TypeUseLocation.LOWER_BOUND})
@SubtypeOf({})
@Documented
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
public @interface InvTop {}
