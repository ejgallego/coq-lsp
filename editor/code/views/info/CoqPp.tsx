export function CoqPp({
  content,
  inline,
}: {
  content: string;
  inline: boolean;
}) {
  if (inline) {
    return <code style={{ whiteSpace: "pre" }}>{content}</code>;
  } else {
    return <pre>{content}</pre>;
  }
}
