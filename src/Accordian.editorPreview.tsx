import { Component, ReactNode, createElement } from "react";
import { AccordianPreviewProps } from "../typings/AccordianProps";

export class preview extends Component<AccordianPreviewProps> {
    render(): ReactNode {
        return <div ></div>;
    }
}

export function getPreviewCss(): string {
    return require("./ui/Accordian.css");
}
