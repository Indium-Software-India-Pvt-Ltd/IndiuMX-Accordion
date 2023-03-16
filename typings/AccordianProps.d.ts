/**
 * This file was generated from Accordian.xml
 * WARNING: All changes made to this file will be overwritten
 * @author Mendix Widgets Framework Team
 */
import { ComponentType, CSSProperties, ReactNode } from "react";
import { ActionValue, EditableValue } from "mendix";

export interface AccordianContainerProps {
    name: string;
    class: string;
    style?: CSSProperties;
    tabIndex?: number;
    heading?: EditableValue<string>;
    boolean: boolean;
    onEnter?: ActionValue;
    onExit?: ActionValue;
    content?: ReactNode;
}

export interface AccordianPreviewProps {
    /**
     * @deprecated Deprecated since version 9.18.0. Please use class property instead.
     */
    className: string;
    class: string;
    style: string;
    styleObject?: CSSProperties;
    readOnly: boolean;
    heading: string;
    boolean: boolean;
    onEnter: {} | null;
    onExit: {} | null;
    content: { widgetCount: number; renderer: ComponentType<{ caption?: string }> };
}
